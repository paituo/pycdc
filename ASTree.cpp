#include <cstring>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <sstream>
//#define BLOCK_DEBUG
#include <unordered_set>
#include "ASTree.h"
#include "FastStack.h"
#include "pyc_numeric.h"
#include "pyc_sequence.h"
#include "pyc_string.h"
#include "bytecode.h"

// This must be a triple quote (''' or """), to handle interpolated string literals containing the opposite quote style.
// E.g. f'''{"interpolated "123' literal"}'''    -> valid.
// E.g. f"""{"interpolated "123' literal"}"""    -> valid.
// E.g. f'{"interpolated "123' literal"}'        -> invalid, unescaped quotes in literal.
// E.g. f'{"interpolated \"123\' literal"}'      -> invalid, f-string expression does not allow backslash.
// NOTE: Nested f-strings not supported.
#define F_STRING_QUOTE "'''"

static void append_to_chain_store(const PycRef<ASTNode>& chainStore,
        PycRef<ASTNode> item, FastStack& stack, const PycRef<ASTBlock>& curblock);

/* Use this to determine if an error occurred (and therefore, if we should
 * avoid cleaning the output tree) */
static bool cleanBuild;

/* Use this to prevent printing return keywords and newlines in lambdas. */
static bool inLambda = false;

/* Use this to keep track of whether we need to print out any docstring and
 * the list of global variables that we are using (such as inside a function). */
static bool printDocstringAndGlobals = false;

/* Use this to keep track of whether we need to print a class or module docstring */
static bool printClassDocstring = true;

// shortcut for all top/pop calls
static PycRef<ASTNode> StackPopTop(FastStack& stack)
{
    const auto node(stack.top());
    stack.pop();
    return node;
}

/* compiler generates very, VERY similar byte code for if/else statement block and if-expression
 *  statement
 *      if a: b = 1
 *      else: b = 2
 *  expression:
 *      b = 1 if a else 2
 *  (see for instance https://stackoverflow.com/a/52202007)
 *  here, try to guess if just finished else statement is part of if-expression (ternary operator)
 *  if it is, remove statements from the block and put a ternary node on top of stack
 */
static PycRef<ASTNode> ExtractExprFromReturn(PycRef<ASTBlock> block)
{
    if (block->nodes().empty())
        return PycRef<ASTNode>();
    auto last = block->nodes().back();
    if (last.type() == ASTNode::NODE_RETURN) {
        auto ret = last.try_cast<ASTReturn>();
        if (ret) {
            PycRef<ASTNode> val = ret->value();
            block->removeLast();
            return val;
        }
    }
    return PycRef<ASTNode>();
}

static void CheckIfExpr(FastStack& stack, PycRef<ASTBlock> curblock)
{
    if (curblock->nodes().size() < 2)
        return;
    auto rit = curblock->nodes().crbegin();
    // the last is "else" block, the one before should be "if" (could be "for", ...)
    if ((*rit)->type() != ASTNode::NODE_BLOCK ||
        (*rit).cast<ASTBlock>()->blktype() != ASTBlock::BLK_ELSE)
        return;
    ++rit;
    if ((*rit)->type() != ASTNode::NODE_BLOCK ||
        (*rit).cast<ASTBlock>()->blktype() != ASTBlock::BLK_IF)
        return;
    auto else_block = *(--rit);

    /* In lambdas, both branches of a ternary end with RETURN_VALUE (consuming
     * the expression value from the stack). Extract the values from the
     * ASTReturn nodes inside each block instead of popping the value stack. */
    PycRef<ASTNode> else_expr;
    if (inLambda) {
        else_expr = ExtractExprFromReturn(else_block.cast<ASTBlock>());
    }
    if (!else_expr) {
        if (stack.empty()) return;
        else_expr = StackPopTop(stack);
    }

    curblock->removeLast(); // remove BLK_ELSE

    auto if_block = curblock->nodes().back();

    PycRef<ASTNode> if_expr;
    if (inLambda) {
        if_expr = ExtractExprFromReturn(if_block.cast<ASTBlock>());
    }
    if (!if_expr) {
        if (stack.empty()) return;
        if_expr = StackPopTop(stack);
    }

    curblock->removeLast(); // remove BLK_IF
    stack.push(new ASTTernary(std::move(if_block), std::move(if_expr), std::move(else_expr)));
}

PycRef<ASTNode> BuildFromCode(PycRef<PycCode> code, PycModule* mod)
{
    try {
    PycBuffer source(code->code()->value(), code->code()->length());

    FastStack stack((mod->majorVer() == 1) ? 20 : code->stackSize());
    stackhist_t stack_hist;

    std::stack<PycRef<ASTBlock> > blocks;
    PycRef<ASTBlock> defblock = new ASTBlock(ASTBlock::BLK_MAIN);
    defblock->init();
    PycRef<ASTBlock> curblock = defblock;
    blocks.push(defblock);

    int opcode, operand;
    int curpos = 0;
    int pos = 0;
    int unpack = 0;
    bool else_pop = false;
    bool need_try = false;
    bool variable_annotations = false;
    bool unsupportedOpcode = false;
    bool defer_try_pop = false;            /* Python 3.10+: set to defer BLK_TRY pop when a with
                                            * block's __exit__ cleanup was just skipped */
    std::vector<PycExceptionTableEntry> exception_entries;
    size_t next_exception_entry = 0;

    if (mod->verCompare(3, 11) >= 0) {
        exception_entries = code->exceptionTableEntries();
    }

    while (!source.atEof()) {
#if defined(BLOCK_DEBUG) || defined(STACK_DEBUG)
        fprintf(stderr, "%-7d", pos);
    #ifdef STACK_DEBUG
        fprintf(stderr, "%-5d", (unsigned int)stack_hist.size() + 1);
    #endif
    #ifdef BLOCK_DEBUG
        for (unsigned int i = 0; i < blocks.size(); i++)
            fprintf(stderr, "    ");
        fprintf(stderr, "%s (%d)", curblock->type_str(), curblock->end());
    #endif
        fprintf(stderr, "\n");
#endif

        while (next_exception_entry < exception_entries.size()
                && exception_entries[next_exception_entry].start_offset < pos) {
            next_exception_entry++;
        }

        if (next_exception_entry < exception_entries.size()) {
            const auto& entry = exception_entries[next_exception_entry];
            if (entry.start_offset == pos
                    && entry.stack_depth == 0
                    && !entry.push_lasti) {
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    curblock.cast<ASTContainerBlock>()->setExcept(entry.target);
                } else {
                    PycRef<ASTBlock> next = new ASTContainerBlock(0, entry.target);
                    blocks.push(next.cast<ASTBlock>());
                    curblock = blocks.top();
                }

                stack_hist.push(stack);
                PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, entry.target, true);
                blocks.push(tryblock.cast<ASTBlock>());
                curblock = blocks.top();
                next_exception_entry++;
            }
        }

        if (curblock->blktype() == ASTBlock::BLK_TRY
                && curblock->end() == pos
                && blocks.size() > 1) {
            PycRef<ASTBlock> prev = curblock;
            blocks.pop();
            curblock = blocks.top();

            if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && (curblock.cast<ASTContainerBlock>()->hasExcept()
                        || mod->verCompare(3, 8) >= 0)) {
                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                }

                curblock->append(prev.cast<ASTNode>());
                stack_hist.push(stack);

                PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                except->init();
                blocks.push(except);
                curblock = blocks.top();
            } else {
                blocks.push(prev);
                curblock = prev;
            }
        }

        if (curblock->blktype() == ASTBlock::BLK_EXCEPT
                && curblock->end() == pos
                && blocks.size() > 1) {
            PycRef<ASTBlock> prev = curblock;
            blocks.pop();
            curblock = blocks.top();

            if (!stack_hist.empty()) {
                stack = stack_hist.top();
                stack_hist.pop();
            }

            if (prev->size() != 0) {
                curblock->append(prev.cast<ASTNode>());
            }

            if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && !curblock.cast<ASTContainerBlock>()->hasFinally()) {
                PycRef<ASTBlock> cont = curblock;
                blocks.pop();
                curblock = blocks.top();
                curblock->append(cont.cast<ASTNode>());
            }
        }

        curpos = pos;
        bc_next(source, mod, opcode, operand, pos);

        if (need_try && opcode != Pyc::SETUP_EXCEPT_A) {
            need_try = false;

            /* Store the current stack for the except/finally statement(s) */
            stack_hist.push(stack);
            PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, curblock->end(), true);
            blocks.push(tryblock);
            curblock = blocks.top();
        } else if (else_pop
                && opcode != Pyc::JUMP_FORWARD_A
                && opcode != Pyc::JUMP_IF_FALSE_A
                && opcode != Pyc::JUMP_IF_FALSE_OR_POP_A
                && opcode != Pyc::POP_JUMP_IF_FALSE_A
                && opcode != Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                && opcode != Pyc::JUMP_IF_TRUE_A
                && opcode != Pyc::JUMP_IF_TRUE_OR_POP_A
                && opcode != Pyc::POP_JUMP_IF_TRUE_A
                && opcode != Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                && opcode != Pyc::POP_BLOCK) {
            else_pop = false;

            PycRef<ASTBlock> prev = curblock;
            while (prev->end() < pos
                    && prev->blktype() != ASTBlock::BLK_MAIN) {
                if (prev->blktype() != ASTBlock::BLK_CONTAINER) {
                    if (prev->end() == 0) {
                        break;
                    }

                    /* We want to keep the stack the same, but we need to pop
                     * a level off the history. */
                    //stack = stack_hist.top();
                    if (!stack_hist.empty())
                        stack_hist.pop();
                }
                blocks.pop();

                if (blocks.empty()) {
                    curblock = defblock;
                    blocks.push(defblock);
                    break;
                }

                curblock = blocks.top();
                curblock->append(prev.cast<ASTNode>());

                prev = curblock;

                CheckIfExpr(stack, curblock);
            }
        }

        switch (opcode) {
        case Pyc::BINARY_OP_A:
            {
                ASTBinary::BinOp op = ASTBinary::from_binary_op(operand);
                if (op == ASTBinary::BIN_INVALID)
                    fprintf(stderr, "Unsupported `BINARY_OP` operand value: %d\n", operand);
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                stack.push(new ASTBinary(left, right, op));
            }
            break;
        case Pyc::BINARY_ADD:
        case Pyc::BINARY_AND:
        case Pyc::BINARY_DIVIDE:
        case Pyc::BINARY_FLOOR_DIVIDE:
        case Pyc::BINARY_LSHIFT:
        case Pyc::BINARY_MODULO:
        case Pyc::BINARY_MULTIPLY:
        case Pyc::BINARY_OR:
        case Pyc::BINARY_POWER:
        case Pyc::BINARY_RSHIFT:
        case Pyc::BINARY_SUBTRACT:
        case Pyc::BINARY_TRUE_DIVIDE:
        case Pyc::BINARY_XOR:
        case Pyc::BINARY_MATRIX_MULTIPLY:
        case Pyc::INPLACE_ADD:
        case Pyc::INPLACE_AND:
        case Pyc::INPLACE_DIVIDE:
        case Pyc::INPLACE_FLOOR_DIVIDE:
        case Pyc::INPLACE_LSHIFT:
        case Pyc::INPLACE_MODULO:
        case Pyc::INPLACE_MULTIPLY:
        case Pyc::INPLACE_OR:
        case Pyc::INPLACE_POWER:
        case Pyc::INPLACE_RSHIFT:
        case Pyc::INPLACE_SUBTRACT:
        case Pyc::INPLACE_TRUE_DIVIDE:
        case Pyc::INPLACE_XOR:
        case Pyc::INPLACE_MATRIX_MULTIPLY:
            {
                ASTBinary::BinOp op = ASTBinary::from_opcode(opcode);
                if (op == ASTBinary::BIN_INVALID)
                    throw std::runtime_error("Unhandled opcode from ASTBinary::from_opcode");
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                stack.push(new ASTBinary(left, right, op));
            }
            break;
        case Pyc::BINARY_SUBSCR:
            {
                PycRef<ASTNode> subscr = stack.top();
                stack.pop();
                PycRef<ASTNode> src = stack.top();
                stack.pop();
                stack.push(new ASTSubscr(src, subscr));
            }
            break;
        case Pyc::BREAK_LOOP:
            curblock->append(new ASTKeyword(ASTKeyword::KW_BREAK));
            break;
        case Pyc::BUILD_CLASS:
            {
                PycRef<ASTNode> class_code = stack.top();
                stack.pop();
                PycRef<ASTNode> bases = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTClass(class_code, bases, name));
            }
            break;
        case Pyc::BUILD_FUNCTION:
            {
                PycRef<ASTNode> fun_code = stack.top();
                stack.pop();
                stack.push(new ASTFunction(fun_code, {}, {}));
            }
            break;
        case Pyc::BUILD_LIST_A:
            {
                ASTList::value_t values;
                for (int i=0; i<operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTList(values));
            }
            break;
        case Pyc::BUILD_SET_A:
            {
                ASTSet::value_t values;
                for (int i=0; i<operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTSet(values));
            }
            break;
        case Pyc::BUILD_MAP_A:
            if (mod->verCompare(3, 5) >= 0) {
                auto map = new ASTMap;
                for (int i=0; i<operand; ++i) {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    map->add(key, value);
                }
                stack.push(map);
            } else {
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                stack.push(new ASTMap());
            }
            break;
        case Pyc::BUILD_CONST_KEY_MAP_A:
            // Top of stack will be a tuple of keys.
            // Values will start at TOS - 1.
            {
                PycRef<ASTNode> keys = stack.top();
                stack.pop();

                ASTConstMap::values_t values;
                values.reserve(operand);
                for (int i = 0; i < operand; ++i) {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    values.push_back(value);
                }

                stack.push(new ASTConstMap(keys, values));
            }
            break;
        case Pyc::STORE_MAP:
            {
                PycRef<ASTNode> key = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                PycRef<ASTMap> map = stack.top().cast<ASTMap>();
                map->add(key, value);
            }
            break;
        case Pyc::DICT_MERGE_A:
        case Pyc::DICT_UPDATE_A:
            {
                PycRef<ASTNode> merge_dict = stack.top();
                stack.pop();
                // Merge the popped dict's items into the map below on stack
                if (merge_dict != NULL && merge_dict.type() == ASTNode::NODE_MAP) {
                    auto src_map = merge_dict.cast<ASTMap>();
                    if (!stack.empty()) {
                        PycRef<ASTNode> target = stack.top();
                        if (target.type() == ASTNode::NODE_MAP) {
                            auto dst_map = target.cast<ASTMap>();
                            for (auto& item : src_map->values()) {
                                dst_map->add(item.first, item.second);
                            }
                        }
                    }
                }
            }
            break;
        case Pyc::BUILD_SLICE_A:
            {
                if (operand == 2) {
                    PycRef<ASTNode> end = stack.top();
                    stack.pop();
                    PycRef<ASTNode> start = stack.top();
                    stack.pop();

                    if (start.type() == ASTNode::NODE_OBJECT
                            && start.cast<ASTObject>()->object() == Pyc_None) {
                        start = NULL;
                    }

                    if (end.type() == ASTNode::NODE_OBJECT
                            && end.cast<ASTObject>()->object() == Pyc_None) {
                        end = NULL;
                    }

                    if (start == NULL && end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE0));
                    } else if (start == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE2, start, end));
                    } else if (end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, start, end));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, start, end));
                    }
                } else if (operand == 3) {
                    PycRef<ASTNode> step = stack.top();
                    stack.pop();
                    PycRef<ASTNode> end = stack.top();
                    stack.pop();
                    PycRef<ASTNode> start = stack.top();
                    stack.pop();

                    if (start.type() == ASTNode::NODE_OBJECT
                            && start.cast<ASTObject>()->object() == Pyc_None) {
                        start = NULL;
                    }

                    if (end.type() == ASTNode::NODE_OBJECT
                            && end.cast<ASTObject>()->object() == Pyc_None) {
                        end = NULL;
                    }

                    if (step.type() == ASTNode::NODE_OBJECT
                            && step.cast<ASTObject>()->object() == Pyc_None) {
                        step = NULL;
                    }

                    /* We have to do this as a slice where one side is another slice */
                    /* [[a:b]:c] */

                    if (start == NULL && end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE0));
                    } else if (start == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE2, start, end));
                    } else if (end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, start, end));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, start, end));
                    }

                    PycRef<ASTNode> lhs = stack.top();
                    stack.pop();

                    if (step == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, lhs, step));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, lhs, step));
                    }
                }
            }
            break;
        case Pyc::BUILD_STRING_A:
            {
                // Nearly identical logic to BUILD_LIST
                ASTList::value_t values;
                for (int i = 0; i < operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTJoinedStr(values));
            }
            break;
        case Pyc::BUILD_TUPLE_A:
            {
                // if class is a closure code, ignore this tuple
                PycRef<ASTNode> tos = stack.top();
                if (tos && tos->type() == ASTNode::NODE_LOADBUILDCLASS) {
                    break;
                }

                ASTTuple::value_t values;
                values.resize(operand);
                for (int i=0; i<operand; i++) {
                    values[operand-i-1] = stack.top();
                    stack.pop();
                }
                stack.push(new ASTTuple(values));
            }
            break;
        case Pyc::LIST_TO_TUPLE:
            {
                PycRef<ASTNode> list_node = stack.top();
                stack.pop();
                ASTTuple::value_t values;
                if (list_node.type() == ASTNode::NODE_LIST) {
                    auto list = list_node.cast<ASTList>();
                    for (auto& v : list->values()) {
                        values.push_back(v);
                    }
                }
                stack.push(new ASTTuple(values));
            }
            break;
        case Pyc::KW_NAMES_A:
            {

                int kwparams = code->getConst(operand).cast<PycTuple>()->size();
                ASTKwNamesMap kwparamList;
                std::vector<PycRef<PycObject>> keys = code->getConst(operand).cast<PycSimpleSequence>()->values();
                for (int i = 0; i < kwparams; i++) {
                    kwparamList.add(new ASTObject(keys[kwparams - i - 1]), stack.top());
                    stack.pop();
                }
                stack.push(new ASTKwNamesMap(kwparamList));
            }
            break;
        case Pyc::CALL_A:
        case Pyc::CALL_FUNCTION_A:
        case Pyc::INSTRUMENTED_CALL_A:
            {
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;

                /* Test for the load build class function */
                stack_hist.push(stack);
                int basecnt = 0;
                ASTTuple::value_t bases;
                bases.resize(basecnt);
                PycRef<ASTNode> TOS = stack.top();
                int TOS_type = TOS.type();
                // bases are NODE_NAME and NODE_BINARY at TOS
                while (TOS_type == ASTNode::NODE_NAME || TOS_type == ASTNode::NODE_BINARY) {
                    bases.resize(basecnt + 1);
                    bases[basecnt] = TOS;
                    basecnt++;
                    stack.pop();
                    TOS = stack.top();
                    TOS_type = TOS.type();
                }
                // qualified name is PycString at TOS
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                PycRef<ASTNode> function = stack.top();
                stack.pop();
                PycRef<ASTNode> loadbuild = stack.top();
                stack.pop();
                int loadbuild_type = loadbuild.type();
                if (loadbuild_type == ASTNode::NODE_LOADBUILDCLASS) {
                    PycRef<ASTNode> call = new ASTCall(function, pparamList, kwparamList);
                    stack.push(new ASTClass(call, new ASTTuple(bases), name));
                    stack_hist.pop();
                    break;
                }
                else
                {
                    stack = stack_hist.top();
                    stack_hist.pop();
                }

                /*
                KW_NAMES(i)
                    Stores a reference to co_consts[consti] into an internal variable for use by CALL.
                    co_consts[consti] must be a tuple of strings.
                    New in version 3.11.
                */
                if (mod->verCompare(3, 11) >= 0) {
                    PycRef<ASTNode> object_or_map = stack.top();
                    if (object_or_map.type() == ASTNode::NODE_KW_NAMES_MAP) {
                        stack.pop();
                        PycRef<ASTKwNamesMap> kwparams_map = object_or_map.cast<ASTKwNamesMap>();
                        for (ASTKwNamesMap::map_t::const_iterator it = kwparams_map->values().begin(); it != kwparams_map->values().end(); it++) {
                            kwparamList.push_front(std::make_pair(it->first, it->second));
                            pparams -= 1;
                        }
                    }
                }
                else {
                    for (int i = 0; i < kwparams; i++) {
                        PycRef<ASTNode> val = stack.top();
                        stack.pop();
                        PycRef<ASTNode> key = stack.top();
                        stack.pop();
                        kwparamList.push_front(std::make_pair(key, val));
                    }
                }
                for (int i=0; i<pparams; i++) {
                    PycRef<ASTNode> param = stack.top();
                    stack.pop();
                    if (param.type() == ASTNode::NODE_FUNCTION) {
                        PycRef<ASTNode> fun_code = param.cast<ASTFunction>()->code();
                        PycRef<PycCode> code_src;
                        if (fun_code.type() == ASTNode::NODE_OBJECT) {
                            code_src = fun_code.cast<ASTObject>()->object().try_cast<PycCode>();
                        }
                        if (code_src) {
                            PycRef<PycString> function_name = code_src->name();
                            if (function_name->isEqual("<lambda>")) {
                                pparamList.push_front(param);
                            } else if (function_name->isEqual("<listcomp>") ||
                                       function_name->isEqual("<setcomp>") ||
                                       function_name->isEqual("<dictcomp>") ||
                                       function_name->isEqual("<genexpr>")) {
                                pparamList.push_front(param);
                            } else {
                                PycRef<ASTNode> decor_name = new ASTName(function_name);
                                curblock->append(new ASTStore(param, decor_name));
                                pparamList.push_front(decor_name);
                            }
                        } else {
                            pparamList.push_front(param);
                        }
                    } else {
                        pparamList.push_front(param);
                    }
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                if ((opcode == Pyc::CALL_A || opcode == Pyc::INSTRUMENTED_CALL_A) &&
                        stack.top() == nullptr) {
                    stack.pop();
                }

                /* Python 3.10+: Detect __exit__(None, None, None) cleanup pattern.
                 * Generated by with-statements on the normal completion path.
                 * func is nullptr because the __exit__ value is implicit on the
                 * Python VM stack but not tracked in pycdc's value stack model. */
                if (mod->verCompare(3, 10) >= 0
                        && func == nullptr
                        && pparams == 3
                        && pparamList.size() == 3) {
                    /* Suppress __exit__(None, None, None); push NULL (None)
                     * as the discarded result. */
                    stack.push(nullptr);
                    break;
                }

                stack.push(new ASTCall(func, pparamList, kwparamList));
            }
            break;
        case Pyc::CALL_FUNCTION_VAR_A:
            {
                PycRef<ASTNode> var = stack.top();
                stack.pop();
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;
                for (int i=0; i<kwparams; i++) {
                    PycRef<ASTNode> val = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    kwparamList.push_front(std::make_pair(key, val));
                }
                for (int i=0; i<pparams; i++) {
                    pparamList.push_front(stack.top());
                    stack.pop();
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                call.cast<ASTCall>()->setVar(var);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_KW_A:
            {
                PycRef<ASTNode> kw_names_node = stack.top();
                stack.pop();

                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;

                if (mod->verCompare(3, 6) >= 0) {
                    int totalArgs = operand;
                    int kwparams = 0;
                    std::vector<PycRef<PycObject>> kw_keys;
                    if (kw_names_node.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> kw_obj = kw_names_node.cast<ASTObject>()->object();
                        if (kw_obj.type() == PycObject::TYPE_TUPLE ||
                            kw_obj.type() == PycObject::TYPE_SMALL_TUPLE) {
                            PycRef<PycSimpleSequence> kw_seq = kw_obj.cast<PycSimpleSequence>();
                            kwparams = kw_seq->size();
                            kw_keys = kw_seq->values();
                        }
                    }
                    int pparams = totalArgs - kwparams;
                    for (int i = kwparams - 1; i >= 0; i--) {
                        PycRef<ASTNode> val = stack.top();
                        stack.pop();
                        PycRef<ASTNode> key = new ASTName(kw_keys[i].cast<PycString>());
                        kwparamList.push_front(std::make_pair(key, val));
                    }
                    for (int i = 0; i < pparams; i++) {
                        pparamList.push_front(stack.top());
                        stack.pop();
                    }
                } else {
                    int kwparams = (operand & 0xFF00) >> 8;
                    int pparams = (operand & 0xFF);
                    for (int i=0; i<kwparams; i++) {
                        PycRef<ASTNode> val = stack.top();
                        stack.pop();
                        PycRef<ASTNode> key = stack.top();
                        stack.pop();
                        kwparamList.push_front(std::make_pair(key, val));
                    }
                    for (int i=0; i<pparams; i++) {
                        pparamList.push_front(stack.top());
                        stack.pop();
                    }
                }

                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_VAR_KW_A:
            {
                PycRef<ASTNode> kw = stack.top();
                stack.pop();
                PycRef<ASTNode> var = stack.top();
                stack.pop();
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;
                for (int i=0; i<kwparams; i++) {
                    PycRef<ASTNode> val = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    kwparamList.push_front(std::make_pair(key, val));
                }
                for (int i=0; i<pparams; i++) {
                    pparamList.push_front(stack.top());
                    stack.pop();
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                call.cast<ASTCall>()->setKW(kw);
                call.cast<ASTCall>()->setVar(var);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_EX_A:
            {
                /* CALL_FUNCTION_EX: func(*args, **kwargs)
                 * operand bit 0: 1 if **kwargs present
                 * Stack: [func, args_tuple, kwargs_dict?] */
                PycRef<ASTNode> kwargs;
                if (operand & 1) {
                    kwargs = stack.top();
                    stack.pop();
                }
                PycRef<ASTNode> args = stack.top();
                stack.pop();
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                ASTCall::pparam_t pparamList;
                ASTCall::kwparam_t kwparamList;

                // Extract positional args from args tuple
                if (args != NULL && args.type() == ASTNode::NODE_TUPLE) {
                    auto tup = args.cast<ASTTuple>();
                    for (auto it = tup->values().begin(); it != tup->values().end(); ++it) {
                        pparamList.push_back(*it);
                    }
                } else if (args != NULL) {
                    pparamList.push_back(args);
                }

                // Extract keyword args from kwargs
                if (kwargs != NULL && kwargs.type() == ASTNode::NODE_MAP) {
                    auto map = kwargs.cast<ASTMap>();
                    for (auto it = map->values().begin(); it != map->values().end(); ++it) {
                        kwparamList.push_back(std::make_pair(it->first, it->second));
                    }
                }

                stack.push(new ASTCall(func, pparamList, kwparamList));
            }
            break;
        case Pyc::CALL_METHOD_A:
            {
                ASTCall::pparam_t pparamList;
                for (int i = 0; i < operand; i++) {
                    PycRef<ASTNode> param = stack.top();
                    stack.pop();
                    if (param.type() == ASTNode::NODE_FUNCTION) {
                        PycRef<ASTNode> fun_code = param.cast<ASTFunction>()->code();
                        PycRef<PycCode> code_src = fun_code.cast<ASTObject>()->object().cast<PycCode>();
                        PycRef<PycString> function_name = code_src->name();
                        if (function_name->isEqual("<lambda>")) {
                            pparamList.push_front(param);
                        } else {
                            // Decorator used
                            PycRef<ASTNode> decor_name = new ASTName(function_name);
                            curblock->append(new ASTStore(param, decor_name));

                            pparamList.push_front(decor_name);
                        }
                    } else {
                        pparamList.push_front(param);
                    }
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                stack.push(new ASTCall(func, pparamList, ASTCall::kwparam_t()));
            }
            break;
        case Pyc::CONTINUE_LOOP_A:
            curblock->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
            break;
        case Pyc::COMPARE_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                auto arg = operand;
                if (mod->verCompare(3, 12) == 0)
                    arg >>= 4; // changed under GH-100923
                else if (mod->verCompare(3, 13) >= 0)
                    arg >>= 5;
                stack.push(new ASTCompare(left, right, arg));
            }
            break;
        case Pyc::CONTAINS_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                // The operand will be 0 for 'in' and 1 for 'not in'.
                stack.push(new ASTCompare(left, right, operand ? ASTCompare::CMP_NOT_IN : ASTCompare::CMP_IN));
            }
            break;
        case Pyc::DELETE_ATTR_A:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                curblock->append(new ASTDelete(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR)));
            }
            break;
        case Pyc::DELETE_GLOBAL_A:
            code->markGlobal(code->getName(operand));
            /* Fall through */
        case Pyc::DELETE_NAME_A:
            {
                PycRef<PycString> varname = code->getName(operand);

                if (varname->length() >= 2 && varname->value()[0] == '_'
                        && varname->value()[1] == '[') {
                    /* Don't show deletes that are a result of list comps. */
                    break;
                }

                PycRef<ASTNode> name = new ASTName(varname);
                curblock->append(new ASTDelete(name));
            }
            break;
        case Pyc::DELETE_FAST_A:
            {
                PycRef<ASTNode> name;

                if (mod->verCompare(1, 3) < 0)
                    name = new ASTName(code->getName(operand));
                else
                    name = new ASTName(code->getLocal(operand));

                if (name.cast<ASTName>()->name()->value()[0] == '_'
                        && name.cast<ASTName>()->name()->value()[1] == '[') {
                    /* Don't show deletes that are a result of list comps. */
                    break;
                }

                curblock->append(new ASTDelete(name));
            }
            break;
        case Pyc::DELETE_DEREF_A:
            {
                if (mod->verCompare(3, 0) >= 0) {
                    PycRef<ASTNode> name = new ASTName(code->getCellVar(mod, operand));
                    curblock->append(new ASTDelete(name));
                }
            }
            break;
        case Pyc::DELETE_SLICE_0:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE0))));
            }
            break;
        case Pyc::DELETE_SLICE_1:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE1, upper))));
            }
            break;
        case Pyc::DELETE_SLICE_2:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE2, NULL, lower))));
            }
            break;
        case Pyc::DELETE_SLICE_3:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE3, upper, lower))));
            }
            break;
        case Pyc::DELETE_SUBSCR:
            {
                PycRef<ASTNode> key = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, key)));
            }
            break;
        case Pyc::DUP_TOP:
            {
                if (stack.top().type() == PycObject::TYPE_NULL) {
                    stack.push(stack.top());
                } else if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    auto chainstore = stack.top();
                    stack.pop();
                    stack.push(stack.top());
                    stack.push(chainstore);
                } else {
                    stack.push(stack.top());
                    ASTNodeList::list_t targets;
                    stack.push(new ASTChainStore(targets, stack.top()));
                }
            }
            break;
        case Pyc::DUP_TOP_TWO:
            {
                PycRef<ASTNode> first = stack.top();
                stack.pop();
                PycRef<ASTNode> second = stack.top();

                stack.push(first);
                stack.push(second);
                stack.push(first);
            }
            break;
        case Pyc::DUP_TOPX_A:
            {
                std::stack<PycRef<ASTNode> > first;
                std::stack<PycRef<ASTNode> > second;

                for (int i = 0; i < operand; i++) {
                    PycRef<ASTNode> node = stack.top();
                    stack.pop();
                    first.push(node);
                    second.push(node);
                }

                while (first.size()) {
                    stack.push(first.top());
                    first.pop();
                }

                while (second.size()) {
                    stack.push(second.top());
                    second.pop();
                }
            }
            break;
        case Pyc::END_FINALLY:
            {
                bool isFinally = false;
                if (curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    PycRef<ASTBlock> final = curblock;
                    blocks.pop();

                    stack = stack_hist.top();
                    stack_hist.pop();

                    curblock = blocks.top();
                    curblock->append(final.cast<ASTNode>());
                    isFinally = true;
                } else if (curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                    blocks.pop();
                    PycRef<ASTBlock> prev = curblock;

                    bool isUninitAsyncFor = false;
                    if (blocks.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                        auto container = blocks.top();
                        blocks.pop();
                        auto asyncForBlock = blocks.top();
                        isUninitAsyncFor = asyncForBlock->blktype() == ASTBlock::BLK_ASYNCFOR && !asyncForBlock->inited();
                        if (isUninitAsyncFor) {
                            auto tryBlock = container->nodes().front().cast<ASTBlock>();
                            if (!tryBlock->nodes().empty() && tryBlock->blktype() == ASTBlock::BLK_TRY) {
                                auto store = tryBlock->nodes().front().try_cast<ASTStore>();
                                if (store) {
                                    asyncForBlock.cast<ASTIterBlock>()->setIndex(store->dest());
                                }
                            }
                            curblock = blocks.top();
                            stack = stack_hist.top();
                            stack_hist.pop();
                            if (!curblock->inited())
                                fprintf(stderr, "Error when decompiling 'async for'.\n");
                        } else {
                            blocks.push(container);
                        }
                    }

                    if (!isUninitAsyncFor) {
                        if (curblock->size() != 0) {
                            blocks.top()->append(curblock.cast<ASTNode>());
                        }

                        curblock = blocks.top();

                        /* Turn it into an else statement. */
                        if (curblock->end() != pos || curblock.cast<ASTContainerBlock>()->hasFinally()) {
                            PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, prev->end());
                            elseblk->init();
                            blocks.push(elseblk);
                            curblock = blocks.top();
                        }
                        else {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                    }
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    /* This marks the end of the except block(s). */
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (!cont->hasFinally() || isFinally) {
                        /* If there's no finally block, pop the container. */
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());
                    }
                }
            }
            break;
        case Pyc::EXEC_STMT:
            {
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> loc = stack.top();
                stack.pop();
                PycRef<ASTNode> glob = stack.top();
                stack.pop();
                PycRef<ASTNode> stmt = stack.top();
                stack.pop();

                curblock->append(new ASTExec(stmt, glob, loc));
            }
            break;
        case Pyc::FOR_ITER_A:
        case Pyc::INSTRUMENTED_FOR_ITER_A:
            {
                PycRef<ASTNode> iter = stack.top(); // Iterable
                if (mod->verCompare(3, 12) < 0) {
                    // Do not pop the iterator for py 3.12+
                    stack.pop();
                }
                /* Pop it? Don't pop it? */

                int end;
                bool comprehension = false;

                // before 3.8, there is a SETUP_LOOP instruction with block start and end position,
                //    the operand is usually a jump to a POP_BLOCK instruction
                // after 3.8, block extent has to be inferred implicitly; the operand is a jump to a position after the for block
                if (mod->majorVer() == 3 && mod->minorVer() >= 8) {
                    end = operand;
                    if (mod->verCompare(3, 10) >= 0)
                        end *= sizeof(uint16_t); // // BPO-27129
                    end += pos;
                    comprehension = strcmp(code->name()->value(), "<listcomp>") == 0;
                } else {
                    PycRef<ASTBlock> top = blocks.top();
                    end = top->end(); // block end position from SETUP_LOOP
                    if (top->blktype() == ASTBlock::BLK_WHILE) {
                        blocks.pop();
                    } else {
                        comprehension = true;
                    }
                }

                PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_FOR, curpos, end, iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();

                stack.push(NULL);
            }
            break;
        case Pyc::FOR_LOOP_A:
            {
                PycRef<ASTNode> curidx = stack.top(); // Current index
                stack.pop();
                PycRef<ASTNode> iter = stack.top(); // Iterable
                stack.pop();

                bool comprehension = false;
                PycRef<ASTBlock> top = blocks.top();
                if (top->blktype() == ASTBlock::BLK_WHILE) {
                    blocks.pop();
                } else {
                    comprehension = true;
                }
                PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_FOR, curpos, top->end(), iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();

                /* Python Docs say:
                      "push the sequence, the incremented counter,
                       and the current item onto the stack." */
                stack.push(iter);
                stack.push(curidx);
                stack.push(NULL); // We can totally hack this >_>
            }
            break;
        case Pyc::GET_AITER:
            {
                // Logic similar to FOR_ITER_A
                PycRef<ASTNode> iter = stack.top(); // Iterable
                stack.pop();

                PycRef<ASTBlock> top = blocks.top();
                if (top->blktype() == ASTBlock::BLK_WHILE) {
                    blocks.pop();
                    PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_ASYNCFOR, curpos, top->end(), iter);
                    blocks.push(forblk.cast<ASTBlock>());
                    curblock = blocks.top();
                    stack.push(nullptr);
                } else {
                     fprintf(stderr, "Unsupported use of GET_AITER outside of SETUP_LOOP\n");
                }
            }
            break;
        case Pyc::GET_ANEXT:
            break;
        case Pyc::FORMAT_VALUE_A:
            {
                auto conversion_flag = static_cast<ASTFormattedValue::ConversionFlag>(operand);
                PycRef<ASTNode> format_spec = nullptr;
                if (conversion_flag & ASTFormattedValue::HAVE_FMT_SPEC) {
                    format_spec = stack.top();
                    stack.pop();
                }
                auto val = stack.top();
                stack.pop();
                stack.push(new ASTFormattedValue(val, conversion_flag, format_spec));
            }
            break;
        case Pyc::GET_AWAITABLE:
            {
                PycRef<ASTNode> object = stack.top();
                stack.pop();
                stack.push(new ASTAwaitable(object));
            }
            break;
        case Pyc::GET_ITER:
        case Pyc::GET_YIELD_FROM_ITER:
            /* We just entirely ignore this */
            break;
        case Pyc::IMPORT_NAME_A:
            if (mod->majorVer() == 1) {
                stack.push(new ASTImport(new ASTName(code->getName(operand)), NULL));
            } else {
                PycRef<ASTNode> fromlist = stack.top();
                stack.pop();
                if (mod->verCompare(2, 5) >= 0)
                    stack.pop();    // Level -- we don't care
                stack.push(new ASTImport(new ASTName(code->getName(operand)), fromlist));
            }
            break;
        case Pyc::IMPORT_FROM_A:
            stack.push(new ASTName(code->getName(operand)));
            break;
        case Pyc::IMPORT_STAR:
            {
                PycRef<ASTNode> import = stack.top();
                stack.pop();
                curblock->append(new ASTStore(import, NULL));
            }
            break;
        case Pyc::IS_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                // The operand will be 0 for 'is' and 1 for 'is not'.
                stack.push(new ASTCompare(left, right, operand ? ASTCompare::CMP_IS_NOT : ASTCompare::CMP_IS));
            }
            break;
        case Pyc::JUMP_IF_FALSE_A:
        case Pyc::JUMP_IF_TRUE_A:
        case Pyc::JUMP_IF_FALSE_OR_POP_A:
        case Pyc::JUMP_IF_TRUE_OR_POP_A:
        case Pyc::POP_JUMP_IF_FALSE_A:
        case Pyc::POP_JUMP_IF_TRUE_A:
        case Pyc::POP_JUMP_FORWARD_IF_FALSE_A:
        case Pyc::POP_JUMP_FORWARD_IF_TRUE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A:
            {
                PycRef<ASTNode> cond = stack.top();
                PycRef<ASTCondBlock> ifblk;
                int popped = ASTCondBlock::UNINITED;

                if (opcode == Pyc::POP_JUMP_IF_FALSE_A
                        || opcode == Pyc::POP_JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A) {
                    /* Pop condition before the jump */
                    stack.pop();
                    popped = ASTCondBlock::PRE_POPPED;
                }

                /* Store the current stack for the else statement(s) */
                stack_hist.push(stack);

                if (opcode == Pyc::JUMP_IF_FALSE_OR_POP_A
                        || opcode == Pyc::JUMP_IF_TRUE_OR_POP_A) {
                    /* Pop condition only if condition is met */
                    stack.pop();
                    popped = ASTCondBlock::POPPED;
                }

                /* "Jump if true" means "Jump if not false" */
                bool neg = opcode == Pyc::JUMP_IF_TRUE_A
                        || opcode == Pyc::JUMP_IF_TRUE_OR_POP_A
                        || opcode == Pyc::POP_JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A;

                int offs = operand;
                if (mod->verCompare(3, 10) >= 0)
                    offs *= sizeof(uint16_t); // // BPO-27129
                if (mod->verCompare(3, 12) >= 0
                        || opcode == Pyc::JUMP_IF_FALSE_A
                        || opcode == Pyc::JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A) {
                    /* Offset is relative in these cases */
                    offs += pos;
                }

                if (cond.type() == ASTNode::NODE_COMPARE
                        && cond.cast<ASTCompare>()->op() == ASTCompare::CMP_EXCEPTION) {
                    int except_end = offs;
                    if (curblock->blktype() == ASTBlock::BLK_EXCEPT
                            && curblock.cast<ASTCondBlock>()->cond() == NULL) {
                        except_end = curblock->end();
                        blocks.pop();
                        curblock = blocks.top();

                        stack_hist.pop();
                    }

                    ifblk = new ASTCondBlock(ASTBlock::BLK_EXCEPT, except_end, cond.cast<ASTCompare>()->right(), false);
                } else if (curblock->blktype() == ASTBlock::BLK_ELSE
                           && curblock->size() == 0
                           && !(inLambda && (mod->verCompare(3, 10) >= 0))) {
                    /* Collapse into elif statement (except in lambdas on 3.10+
                     * where BLK_ELSE with size()==0 represents a ternary else
                     * branch, not an elif candidate). */
                    blocks.pop();
                    stack = stack_hist.top();
                    stack_hist.pop();
                    ifblk = new ASTCondBlock(ASTBlock::BLK_ELIF, offs, cond, neg);
                } else if (curblock->size() == 0 && !curblock->inited()
                           && curblock->blktype() == ASTBlock::BLK_WHILE) {
                    /* The condition for a while loop */
                    PycRef<ASTBlock> top = blocks.top();
                    blocks.pop();
                    ifblk = new ASTCondBlock(top->blktype(), offs, cond, neg);

                    /* We don't store the stack for loops! Pop it! */
                    stack_hist.pop();
                } else if (curblock->size() == 0 && curblock->end() <= offs
                           && (curblock->blktype() == ASTBlock::BLK_IF
                           || curblock->blktype() == ASTBlock::BLK_ELIF
                           || curblock->blktype() == ASTBlock::BLK_WHILE)) {
                    PycRef<ASTNode> newcond;
                    PycRef<ASTCondBlock> top = curblock.cast<ASTCondBlock>();
                    PycRef<ASTNode> cond1 = top->cond();
                    blocks.pop();

                    if (curblock->blktype() == ASTBlock::BLK_WHILE) {
                        stack_hist.pop();
                    } else {
                        FastStack s_top = stack_hist.top();
                        stack_hist.pop();
                        stack_hist.pop();
                        stack_hist.push(s_top);
                    }

                    if (curblock->end() == offs
                            || (curblock->end() == curpos && !top->negative())) {
                        /* if blah and blah */
                        newcond = new ASTBinary(cond1, cond, ASTBinary::BIN_LOG_AND);
                    } else {
                        /* if blah or blah */
                        newcond = new ASTBinary(cond1, cond, ASTBinary::BIN_LOG_OR);
                    }
                    ifblk = new ASTCondBlock(top->blktype(), offs, newcond, neg);
                } else if (curblock->blktype() == ASTBlock::BLK_FOR
                            && curblock.cast<ASTIterBlock>()->isComprehension()
                            && mod->verCompare(2, 7) >= 0) {
                    /* Comprehension condition */
                    curblock.cast<ASTIterBlock>()->setCondition(cond);
                    stack_hist.pop();
                    // TODO: Handle older python versions, where condition
                    // is laid out a little differently.
                    break;
                } else {
                    /* Plain old if statement */
                    ifblk = new ASTCondBlock(ASTBlock::BLK_IF, offs, cond, neg);
                }

                if (popped)
                    ifblk->init(popped);

                blocks.push(ifblk.cast<ASTBlock>());
                curblock = blocks.top();
            }
            break;
        case Pyc::JUMP_ABSOLUTE_A:
        // bpo-47120: Replaced JUMP_ABSOLUTE by the relative jump JUMP_BACKWARD.
        case Pyc::JUMP_BACKWARD_A:
        case Pyc::JUMP_BACKWARD_NO_INTERRUPT_A:
            {
                int offs = operand;
                if (mod->verCompare(3, 10) >= 0)
                    offs *= sizeof(uint16_t); // // BPO-27129 

                if (offs < pos) {
                    if (curblock->blktype() == ASTBlock::BLK_FOR) {
                        bool is_jump_to_start = offs == curblock.cast<ASTIterBlock>()->start();
                        bool should_pop_for_block = curblock.cast<ASTIterBlock>()->isComprehension();
                        // in v3.8, SETUP_LOOP is deprecated and for blocks aren't terminated by POP_BLOCK, so we add them here
                        bool should_add_for_block = mod->majorVer() == 3 && mod->minorVer() >= 8 && is_jump_to_start && !curblock.cast<ASTIterBlock>()->isComprehension();

                        if (should_pop_for_block || should_add_for_block) {
                            PycRef<ASTNode> top = stack.top();

                            if (top.type() == ASTNode::NODE_COMPREHENSION) {
                                PycRef<ASTComprehension> comp = top.cast<ASTComprehension>();

                                comp->addGenerator(curblock.cast<ASTIterBlock>());
                            }

                            PycRef<ASTBlock> tmp = curblock;
                            blocks.pop();
                            curblock = blocks.top();
                            if (should_add_for_block) {
                                curblock->append(tmp.cast<ASTNode>());
                            }
                        }
                    } else if (curblock->blktype() == ASTBlock::BLK_ELSE) {
                        stack = stack_hist.top();
                        stack_hist.pop();

                        blocks.pop();
                        blocks.top()->append(curblock.cast<ASTNode>());
                        curblock = blocks.top();

                        if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                                && !curblock.cast<ASTContainerBlock>()->hasFinally()) {
                            blocks.pop();
                            blocks.top()->append(curblock.cast<ASTNode>());
                            curblock = blocks.top();
                        }
                    } else {
                        /* Check if any ancestor block is a loop (BLK_WHILE,
                         * BLK_FOR). On Python 3.8+ (no SETUP_LOOP), while
                         * loops may not be detected, and JUMP_BACKWARD would
                         * create an orphan 'continue' outside any loop,
                         * causing SyntaxError. Suppress it in that case. */
                        bool inLoop = false;
                        {
                            std::stack<PycRef<ASTBlock>> copy = blocks;
                            while (!copy.empty()) {
                                auto t = copy.top()->blktype();
                                if (t == ASTBlock::BLK_WHILE
                                        || t == ASTBlock::BLK_FOR) {
                                    inLoop = true;
                                    break;
                                }
                                copy.pop();
                            }
                        }
                        if (inLoop)
                            curblock->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
                    }

                    /* We're in a loop, this jumps back to the start */
                    /* I think we'll just ignore this case... */
                    break; // Bad idea? Probably!
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (cont->hasExcept() && pos < cont->except()) {
                        PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                        except->init();
                        blocks.push(except);
                        curblock = blocks.top();
                    }
                    break;
                }

                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                } else {
                    fprintf(stderr, "Warning: Stack history is empty, something wrong might have happened\n");
                }

                PycRef<ASTBlock> prev = curblock;
                PycRef<ASTBlock> nil;
                bool push = true;

                do {
                    blocks.pop();

                    blocks.top()->append(prev.cast<ASTNode>());

                    if (prev->blktype() == ASTBlock::BLK_IF
                            || prev->blktype() == ASTBlock::BLK_ELIF) {
                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTBlock(ASTBlock::BLK_ELSE, blocks.top()->end());
                        if (prev->inited() == ASTCondBlock::PRE_POPPED) {
                            next->init(ASTCondBlock::PRE_POPPED);
                        }

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_EXCEPT) {
                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_EXCEPT, blocks.top()->end(), NULL, false);
                        next->init();

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_ELSE) {
                        /* Special case */
                        prev = blocks.top();
                        if (!push) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                        push = false;
                    } else {
                        prev = nil;
                    }

                } while (prev != nil);

                curblock = blocks.top();
            }
            break;
        case Pyc::JUMP_FORWARD_A:
        case Pyc::INSTRUMENTED_JUMP_FORWARD_A:
            {
                int offs = operand;
                if (mod->verCompare(3, 10) >= 0)
                    offs *= sizeof(uint16_t); // // BPO-27129

                if (blocks.empty()) {
                    /* blocks stack is empty, nothing to process for this jump */
                    break;
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (cont->hasExcept()) {
                        /* Python 3.10+ defers BLK_EXCEPT creation to
                         * JUMP_IF_NOT_EXC_MATCH when the exception
                         * handler entry is actually reached.  Creating
                         * BLK_EXCEPT here prematurely at the JUMP_FORWARD
                         * would swallow all handler code into a single
                         * BLK_EXCEPT and prevent JUMP_IF_NOT_EXC_MATCH
                         * from setting up the correct BLK_EXCEPT. */
                        if (mod->verCompare(3, 10) >= 0) {
                            break;
                        }
                        stack_hist.push(stack);

                        curblock->setEnd(pos+offs);
                        PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, pos+offs, NULL, false);
                        except->init();
                        blocks.push(except);
                        curblock = blocks.top();
                    }
                    break;
                }

                if (!stack_hist.empty()) {
                    if (stack.empty()) // if it's part of if-expression, TOS at the moment is the result of "if" part
                        stack = stack_hist.top();
                    stack_hist.pop();
                }

                /* Don't pop BLK_TRY if the jump is still within the try body.
                 * This handles ternary expressions inside try/except in Python
                 * 3.10+ (e.g., `msg = choices[0].get('message') if choices else None`
                 * inside a try body).  The JUMP_FORWARD for the false branch of the
                 * ternary is still within the try body and should not close it. */
                if (curblock->blktype() == ASTBlock::BLK_TRY
                        && curblock->end() >= pos+offs) {
                    break;
                }

                PycRef<ASTBlock> prev = curblock;
                PycRef<ASTBlock> nil;
                bool push = true;

                do {
                    blocks.pop();

                    if (!blocks.empty())
                        blocks.top()->append(prev.cast<ASTNode>());

                    if (prev->blktype() == ASTBlock::BLK_IF
                            || prev->blktype() == ASTBlock::BLK_ELIF) {
                        if (offs == 0) {
                            prev = nil;
                            continue;
                        }

                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTBlock(ASTBlock::BLK_ELSE, pos+offs);
                        if (prev->inited() == ASTCondBlock::PRE_POPPED) {
                            next->init(ASTCondBlock::PRE_POPPED);
                        }

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_EXCEPT) {
                        if (offs == 0) {
                            prev = nil;
                            continue;
                        }

                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_EXCEPT, pos+offs, NULL, false);
                        next->init();

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_ELSE) {
                        /* Special case */
                        if (blocks.empty()) {
                            fprintf(stderr, "Warning: JUMP_FORWARD BLK_ELSE with empty blocks at pos=%d\n", pos);
                            fflush(stderr);
                            prev = nil;
                        } else {
                            prev = blocks.top();
                            if (!push) {
                                stack = stack_hist.top();
                                stack_hist.pop();
                            }
                            push = false;

                            if (prev->blktype() == ASTBlock::BLK_MAIN) {
                                /* Something went out of control! */
                                prev = nil;
                            }
                        }
                    } else if (prev->blktype() == ASTBlock::BLK_TRY
                            && prev->end() < pos+offs) {
                        /* Need to add an except/finally block */
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }

                        if (blocks.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                            PycRef<ASTContainerBlock> cont = blocks.top().cast<ASTContainerBlock>();
                            if (cont->hasExcept()) {
                                if (push) {
                                    stack_hist.push(stack);
                                }

                                PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, pos+offs, NULL, false);
                                except->init();
                                blocks.push(except);
                            }
                        } else {
                            fprintf(stderr, "Something TERRIBLE happened!!\n");
                        }
                        prev = nil;
                    } else {
                        prev = nil;
                    }

                } while (prev != nil);

                if (!blocks.empty()) {
                    curblock = blocks.top();
                    if (curblock->blktype() == ASTBlock::BLK_EXCEPT)
                        curblock->setEnd(pos+offs);
                } else {
                    curblock = defblock;
                    blocks.push(defblock);
                }
            }
            break;
        case Pyc::LIST_APPEND:
        case Pyc::LIST_APPEND_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                PycRef<ASTNode> list = stack.top();


                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    stack.pop();
                    stack.push(new ASTComprehension(value));
                } else {
                    stack.push(new ASTSubscr(list, value)); /* Total hack */
                }
            }
            break;
        case Pyc::SET_ADD:
        case Pyc::SET_ADD_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    stack.pop();
                    stack.push(new ASTComprehension(value));
                }
                // For non-comprehension context, just discard value
            }
            break;
        case Pyc::MAP_ADD_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                PycRef<ASTNode> key = stack.top();
                stack.pop();

                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    PycRef<ASTNode> top = stack.top();
                    if (top.type() == ASTNode::NODE_MAP) {
                        top.cast<ASTMap>()->add(key, value);
                    } else {
                        stack.pop();
                        auto map = new ASTMap();
                        map->add(key, value);
                        stack.push(map);
                    }
                }
            }
            break;
        case Pyc::SET_UPDATE_A:
            {
                PycRef<ASTNode> rhs = stack.top();
                stack.pop();
                PycRef<ASTSet> lhs = stack.top().try_cast<ASTSet>();
                stack.pop();

                if (lhs) {
                    ASTSet::value_t result = lhs->values();

                    if (rhs.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> obj = rhs.cast<ASTObject>()->object();
                        if (obj->type() == PycObject::TYPE_FROZENSET) {
                            for (const auto& it : obj.cast<PycSet>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else if (obj->type() == PycObject::TYPE_TUPLE || obj->type() == PycObject::TYPE_SMALL_TUPLE) {
                            for (const auto& it : obj.cast<PycTuple>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else {
                            result.push_back(new ASTUnpack(rhs));
                        }
                    } else if (rhs.type() == ASTNode::NODE_SET) {
                        for (const auto& it : rhs.cast<ASTSet>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_LIST) {
                        for (const auto& it : rhs.cast<ASTList>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_TUPLE) {
                        for (const auto& it : rhs.cast<ASTTuple>()->values()) {
                            result.push_back(it);
                        }
                    } else {
                        result.push_back(new ASTUnpack(rhs));
                    }

                    stack.push(new ASTSet(result));
                } else {
                    ASTSet::value_t result;
                    if (rhs.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> obj = rhs.cast<ASTObject>()->object();
                        if (obj->type() == PycObject::TYPE_FROZENSET) {
                            for (const auto& it : obj.cast<PycSet>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else if (obj->type() == PycObject::TYPE_TUPLE || obj->type() == PycObject::TYPE_SMALL_TUPLE) {
                            for (const auto& it : obj.cast<PycTuple>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else {
                            result.push_back(new ASTUnpack(rhs));
                        }
                    } else if (rhs.type() == ASTNode::NODE_SET) {
                        for (const auto& it : rhs.cast<ASTSet>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_LIST) {
                        for (const auto& it : rhs.cast<ASTList>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_TUPLE) {
                        for (const auto& it : rhs.cast<ASTTuple>()->values()) {
                            result.push_back(it);
                        }
                    } else {
                        result.push_back(new ASTUnpack(rhs));
                    }
                    stack.push(new ASTSet(result));
                }
            }
            break;
        case Pyc::LIST_EXTEND_A:
            {
                PycRef<ASTNode> rhs = stack.top();
                stack.pop();
                PycRef<ASTList> lhs = stack.top().try_cast<ASTList>();
                stack.pop();

                if (lhs) {
                    ASTList::value_t result = lhs->values();

                    if (rhs.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> obj = rhs.cast<ASTObject>()->object();
                        if (obj->type() == PycObject::TYPE_TUPLE || obj->type() == PycObject::TYPE_SMALL_TUPLE) {
                            for (const auto& it : obj.cast<PycTuple>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else if (obj->type() == PycObject::TYPE_LIST) {
                            for (const auto& it : obj.cast<PycList>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else {
                            result.push_back(new ASTUnpack(rhs));
                        }
                    } else if (rhs.type() == ASTNode::NODE_LIST) {
                        for (const auto& it : rhs.cast<ASTList>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_TUPLE) {
                        for (const auto& it : rhs.cast<ASTTuple>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_COMPREHENSION) {
                        result.push_back(new ASTUnpack(rhs));
                    } else {
                        result.push_back(new ASTUnpack(rhs));
                    }

                    stack.push(new ASTList(result));
                } else {
                    ASTList::value_t result;
                    if (rhs.type() == ASTNode::NODE_LIST) {
                        result = rhs.cast<ASTList>()->values();
                    } else if (rhs.type() == ASTNode::NODE_TUPLE) {
                        for (const auto& it : rhs.cast<ASTTuple>()->values()) {
                            result.push_back(it);
                        }
                    } else if (rhs.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> obj = rhs.cast<ASTObject>()->object();
                        if (obj->type() == PycObject::TYPE_TUPLE || obj->type() == PycObject::TYPE_SMALL_TUPLE) {
                            for (const auto& it : obj.cast<PycTuple>()->values()) {
                                result.push_back(new ASTObject(it));
                            }
                        } else {
                            result.push_back(new ASTUnpack(rhs));
                        }
                    } else {
                        result.push_back(new ASTUnpack(rhs));
                    }
                    stack.push(new ASTList(result));
                }
            }
            break;
        case Pyc::LOAD_ATTR_A:
            {
                PycRef<ASTNode> name = stack.top();
                if (name.type() != ASTNode::NODE_IMPORT) {
                    stack.pop();

                    if (mod->verCompare(3, 12) >= 0) {
                        if (operand & 1) {
                            /* Changed in version 3.12:
                            If the low bit of name is set, then a NULL or self is pushed to the stack
                            before the attribute or unbound method respectively. */
                            stack.push(nullptr);
                        }
                        operand >>= 1;
                    }

                    stack.push(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR));
                }
            }
            break;
        case Pyc::LOAD_BUILD_CLASS:
            stack.push(new ASTLoadBuildClass(new PycObject()));
            break;
        case Pyc::LOAD_ASSERTION_ERROR:
            stack.push(nullptr);
            break;
        case Pyc::LOAD_CLOSURE_A:
            /* Python 3.10+: Load a closure variable (cell var) onto the stack
             * for building the closure tuple used by MAKE_FUNCTION with the
             * closure flag (0x08).  This was previously a no-op but is needed
             * to keep the value stack correctly aligned. */
            if (mod->verCompare(3, 10) >= 0) {
                stack.push(new ASTName(code->getCellVar(mod, operand)));
            }
            break;
        case Pyc::LOAD_CONST_A:
            {
                PycRef<ASTObject> t_ob = new ASTObject(code->getConst(operand));

                if ((t_ob->object().type() == PycObject::TYPE_TUPLE ||
                        t_ob->object().type() == PycObject::TYPE_SMALL_TUPLE) &&
                        !t_ob->object().cast<PycTuple>()->values().size()) {
                    ASTTuple::value_t values;
                    stack.push(new ASTTuple(values));
                } else if (t_ob->object().type() == PycObject::TYPE_NONE) {
                    stack.push(NULL);
                } else {
                    stack.push(t_ob.cast<ASTNode>());
                }
            }
            break;
        case Pyc::LOAD_DEREF_A:
        case Pyc::LOAD_CLASSDEREF_A:
            stack.push(new ASTName(code->getCellVar(mod, operand)));
            break;
        case Pyc::LOAD_FAST_A:
            if (mod->verCompare(1, 3) < 0)
                stack.push(new ASTName(code->getName(operand)));
            else
                stack.push(new ASTName(code->getLocal(operand)));
            break;
        case Pyc::LOAD_FAST_LOAD_FAST_A:
            stack.push(new ASTName(code->getLocal(operand >> 4)));
            stack.push(new ASTName(code->getLocal(operand & 0xF)));
            break;
        case Pyc::LOAD_GLOBAL_A:
            if (mod->verCompare(3, 11) >= 0) {
                // Loads the global named co_names[namei>>1] onto the stack.
                if (operand & 1) {
                    /* Changed in version 3.11: 
                    If the low bit of "NAMEI" (operand) is set, 
                    then a NULL is pushed to the stack before the global variable. */
                    stack.push(nullptr);
                }
                operand >>= 1;
            }
            stack.push(new ASTName(code->getName(operand)));
            break;
        case Pyc::LOAD_LOCALS:
            stack.push(new ASTNode(ASTNode::NODE_LOCALS));
            break;
        case Pyc::STORE_LOCALS:
            stack.pop();
            break;
        case Pyc::LOAD_METHOD_A:
            {
                // Behave like LOAD_ATTR
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR));
            }
            break;
        case Pyc::LOAD_NAME_A:
            stack.push(new ASTName(code->getName(operand)));
            break;
        case Pyc::MAKE_CLOSURE_A:
        case Pyc::MAKE_FUNCTION_A:
            {
                PycRef<ASTNode> fun_code = stack.top();
                stack.pop();

                /* Test for the qualified name of the function (at TOS) */
                int tos_type = fun_code.cast<ASTObject>()->object().type();
                if (tos_type != PycObject::TYPE_CODE &&
                    tos_type != PycObject::TYPE_CODE2) {
                    fun_code = stack.top();
                    stack.pop();
                }

                ASTFunction::defarg_t defArgs, kwDefArgs;

                if (mod->verCompare(3, 10) >= 0) {
                    /* Python 3.10+ uses bit flags for the operand:
                     *   0x01 = has defaults tuple      (1 item on stack)
                     *   0x02 = has kwdefaults dict     (1 item on stack)
                     *   0x04 = has annotations tuple   (1 item on stack)
                     *   0x08 = has closure tuple       (1 item on stack)
                     *
                     * Stack layout (bottom to top):
                     *   [... closure_tuple, defaults_tuple, kwdefaults_dict, annotations_tuple, code, qualname]
                     *   where items are present only if the corresponding flag is set.
                     */
                    /* Closure (flags & 0x08) - pop and discard */
                    if (operand & 0x08) {
                        stack.pop();
                    }
                    /* Annotations (flags & 0x04) - pop and discard */
                    if (operand & 0x04) {
                        stack.pop();
                    }
                    /* kwdefaults (flags & 0x02) */
                    if (operand & 0x02) {
                        kwDefArgs.push_front(stack.top());
                        stack.pop();
                    }
                    /* defaults (flags & 0x01) - a tuple on stack, unpack into defArgs */
                    if (operand & 0x01) {
                        PycRef<ASTNode> def_tuple = stack.top();
                        stack.pop();
                        if (def_tuple.type() == ASTNode::NODE_TUPLE) {
                            auto items = def_tuple.cast<ASTTuple>()->values();
                            for (auto it = items.rbegin(); it != items.rend(); ++it) {
                                defArgs.push_front(*it);
                            }
                        } else {
                            defArgs.push_front(def_tuple);
                        }
                    }
                } else {
                    /* Pre-3.10 format: operand encodes defCount (low byte) and kwDefCount (high byte) */
                    const int defCount = operand & 0xFF;
                    const int kwDefCount = (operand >> 8) & 0xFF;
                    for (int i = 0; i < defCount; ++i) {
                        defArgs.push_front(stack.top());
                        stack.pop();
                    }
                    for (int i = 0; i < kwDefCount; ++i) {
                        kwDefArgs.push_front(stack.top());
                        stack.pop();
                    }
                }
                stack.push(new ASTFunction(fun_code, defArgs, kwDefArgs));
            }
            break;
        case Pyc::NOP:
            break;
        case Pyc::POP_BLOCK:
            {
                if (blocks.empty()) {
                    /* blocks stack is empty, nothing to pop */
                    break;
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER ||
                        curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    /* These should only be popped by an END_FINALLY */
                    break;
                }

                /* Python 3.10+: POP_BLOCK ends a with block on the normal
                 * (non-exception) path. Close BLK_WITH properly. */
                if (curblock->blktype() == ASTBlock::BLK_WITH) {
                    PycRef<ASTBlock> with = curblock;
                    blocks.pop();
                    /* NOTE: Do NOT restore stack from stack_hist here!
                     * stack_hist was pushed by need_try (SETUP_FINALLY),
                     * NOT by SETUP_WITH. Restoring it would discard values
                     * computed inside the with body (e.g. return values). */
                    curblock = blocks.top();
                    curblock->append(with.cast<ASTNode>());

                    /* Python 3.10+: The with statement's normal exit generates
                     * an internal __exit__ cleanup sequence that pycdc does not
                     * model in its value stack (the __exit__ method is implicit
                     * in the CPython VM but absent from pycdc's stack model).
                     *
                     * Skip past this cleanup sequence to avoid:
                     * 1. ROT_TWO corrupting the stack (missing __exit__ value)
                     * 2. CALL_FUNCTION 3 operating on wrong/nil values
                     * 3. Stack-history corruption when BLK_TRY is later popped
                     *
                     * The cleanup sequence is:
                     *   [OPTIONAL] ROT_TWO (2 bytes) -- if with body left a value
                     *   LOAD_CONST None (2 bytes)
                     *   DUP_TOP (2 bytes)
                     *   DUP_TOP (2 bytes)
                     *   CALL_FUNCTION 3 (2 bytes)  -- __exit__(None, None, None)
                     *   POP_TOP (2 bytes)
                     * Total: 10-12 bytes
                     *
                     * After POP_TOP, normal processing resumes (POP_BLOCK for
                     * outer BLK_TRY, RETURN_VALUE, etc.) */
                    if (mod->verCompare(3, 10) >= 0) {
                        const char* raw_code = code->code()->value();
                        int raw_len = code->code()->length();
                        int scan_pos = pos;
                        int skip_bytes = 0;

                        if (scan_pos < raw_len) {
                            int ck = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(), (unsigned char)raw_code[scan_pos]);
                            if (ck == Pyc::ROT_TWO) {
                                /* ROT_TWO present: 6 instructions = 12 bytes */
                                skip_bytes = 12;
                                scan_pos += 2;
                            } else if (ck == Pyc::LOAD_CONST_A) {
                                /* No ROT_TWO: 5 instructions = 10 bytes */
                                skip_bytes = 10;
                                scan_pos += 2;
                            }

                            if (skip_bytes > 0) {
                                /* Verify the pattern at the expected positions */
                                bool pattern_valid = true;
                                int verify_offsets[] = {0, 2, 4, 6, 8};
                                int verify_count = 5;
                                if (skip_bytes == 12) {
                                    /* ROT_TWO pattern: offsets 2,4,6,8,10 from scan_pos-2 */
                                    int vops[] = {Pyc::LOAD_CONST_A, Pyc::DUP_TOP,
                                                  Pyc::DUP_TOP, Pyc::CALL_FUNCTION_A,
                                                  Pyc::POP_TOP};
                                    for (int i = 0; i < verify_count; i++) {
                                        if (scan_pos + verify_offsets[i] + 1 < raw_len) {
                                            int vop = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(),
                                                                        (unsigned char)raw_code[scan_pos + verify_offsets[i]]);
                                            if (vop != vops[i]) {
                                                pattern_valid = false;
                                                break;
                                            }
                                        }
                                    }
                                } else {
                                    /* LOAD_CONST pattern: offsets 0,2,4,6,8 from scan_pos */
                                    int vops[] = {Pyc::DUP_TOP, Pyc::DUP_TOP,
                                                  Pyc::CALL_FUNCTION_A, Pyc::POP_TOP};
                                    for (int i = 0; i < 4; i++) {
                                        if (scan_pos + verify_offsets[i] + 1 < raw_len) {
                                            int vop = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(),
                                                                        (unsigned char)raw_code[scan_pos + verify_offsets[i]]);
                                            if (vop != vops[i]) {
                                                pattern_valid = false;
                                                break;
                                            }
                                        }
                                    }
                                }

                                if (pattern_valid) {
                                    /* CRITICAL: skipBytes() must be called to keep
                                     * PycBuffer's internal m_pos in sync with `pos`.
                                     * Without this, bc_next() reads from a stale
                                     * position and all subsequent bytecode processing
                                     * becomes garbage, eventually causing exit(1). */
                                    source.skipBytes(skip_bytes);
                                    pos += skip_bytes;
                                    defer_try_pop = true;
                                    /* Defer the enclosing BLK_TRY pop so that
                                     * continuation code between POP_BLOCK and
                                     * the exception handler (e.g. RETURN_VALUE
                                     * inside the try body) stays in BLK_TRY. */
                                }
                            }
                        }
                    }
                    break;
                }

                if (curblock->nodes().size() &&
                        curblock->nodes().back().type() == ASTNode::NODE_KEYWORD) {
                    curblock->removeLast();
                }

                if (curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELIF
                        || curblock->blktype() == ASTBlock::BLK_ELSE
                        || curblock->blktype() == ASTBlock::BLK_TRY
                        || curblock->blktype() == ASTBlock::BLK_EXCEPT
                        || curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    /* Python 3.10+: POP_BLOCK for BLK_TRY on the normal path
                     * should NOT restore stack from stack_hist. The stack_hist
                     * was saved at try-block entry; restoring it here would
                     * discard values computed inside the try body (e.g. the
                     * return value of a with block). The stack_hist entry is
                     * kept for the exception handler path. */
                    if (!(mod->verCompare(3, 10) >= 0
                            && curblock->blktype() == ASTBlock::BLK_TRY)) {
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        } else {
                            fprintf(stderr, "Warning: Stack history is empty, something wrong might have happened\n");
                        }
                    }
                }
                /* Python 3.10+: Defer BLK_TRY pop at POP_BLOCK when continuation
                 * code (e.g. RETURN_VALUE, STORE_FAST) follows between POP_BLOCK
                 * and the exception handler entry.  Check the next opcode:
                 * if it's JUMP_FORWARD, the handler is being skipped normally;
                 * otherwise, keep BLK_TRY open so continuation code stays in the
                 * try body rather than leaking to the enclosing BLK_CONTAINER. */
                if (defer_try_pop
                        || (mod->verCompare(3, 10) >= 0
                            && curblock->blktype() == ASTBlock::BLK_TRY
                            && curblock->end() > pos)) {
                    /* Peek at the next opcode to decide whether to defer. */
                    const char* raw_code = code->code()->value();
                    int raw_len = code->code()->length();
                    bool should_defer = false;
                    if (pos < raw_len) {
                        int next_op = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(),
                                                        (unsigned char)raw_code[pos]);
                        /* JUMP_FORWARD means the handler is being skipped after
                         * a normal try-body exit.  All other instructions are
                         * continuation code that should remain inside BLK_TRY. */
                        should_defer = (next_op != Pyc::JUMP_FORWARD_A);
                    }
                    if (should_defer) {
                        defer_try_pop = false;
                        break;
                    }
                }
                defer_try_pop = false;

                PycRef<ASTBlock> tmp = curblock;
                blocks.pop();

                if (!blocks.empty()) {
                    curblock = blocks.top();
                } else {
                    curblock = defblock;
                    blocks.push(defblock);
                }

                if (!(tmp->blktype() == ASTBlock::BLK_ELSE
                        && tmp->nodes().size() == 0)) {
                    curblock->append(tmp.cast<ASTNode>());
                }

                if (tmp->blktype() == ASTBlock::BLK_FOR && tmp->end() >= pos) {
                    stack_hist.push(stack);

                    PycRef<ASTBlock> blkelse = new ASTBlock(ASTBlock::BLK_ELSE, tmp->end());
                    blocks.push(blkelse);
                    curblock = blocks.top();
                }

                if (curblock->blktype() == ASTBlock::BLK_TRY
                        && tmp->blktype() != ASTBlock::BLK_FOR
                        && tmp->blktype() != ASTBlock::BLK_ASYNCFOR
                        && tmp->blktype() != ASTBlock::BLK_WHILE
                        && tmp->blktype() != ASTBlock::BLK_TRY) {
                    /* Python 3.10+: Continuation code detection. If POP_BLOCK
                     * popped a child block (e.g., BLK_IF) and the parent is
                     * BLK_TRY, check the next opcode. If it is not JUMP_FORWARD,
                     * there is continuation code (e.g., RETURN_VALUE, STORE_FAST)
                     * that belongs inside the try body. Keep BLK_TRY open and
                     * defer popping to the next POP_BLOCK. */
                    if (mod->verCompare(3, 10) >= 0) {
                        const char* raw_code = code->code()->value();
                        int raw_len = code->code()->length();
                        if (pos < raw_len) {
                            int next_op = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(),
                                                            (unsigned char)raw_code[pos]);
                            if (next_op != Pyc::JUMP_FORWARD_A) {
                                defer_try_pop = true;
                                break;
                            }
                        }
                    }

                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    }

                    tmp = curblock;
                    blocks.pop();

                    if (!blocks.empty()) {
                        curblock = blocks.top();
                        if (!(tmp->blktype() == ASTBlock::BLK_ELSE
                                && tmp->nodes().size() == 0)) {
                            curblock->append(tmp.cast<ASTNode>());
                        }
                    } else {
                        curblock = defblock;
                        blocks.push(defblock);
                    }
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();

                    if (tmp->blktype() == ASTBlock::BLK_ELSE && !cont->hasFinally()) {

                        /* Pop the container */
                        blocks.pop();
                        if (!blocks.empty()) {
                            curblock = blocks.top();
                            curblock->append(cont.cast<ASTNode>());
                        } else {
                            curblock = defblock;
                            blocks.push(defblock);
                            defblock->append(cont.cast<ASTNode>());
                        }

                    } else if (tmp->blktype() == ASTBlock::BLK_TRY && cont->hasExcept()) {
                        /* Python 3.10+: try/except - create BLK_EXCEPT instead of BLK_FINALLY.
                         * For Python 3.10+, defer BLK_EXCEPT creation to JUMP_IF_NOT_EXC_MATCH
                         * when the exception handler is actually reached. Creating BLK_EXCEPT
                         * here at POP_BLOCK is premature because code between POP_BLOCK and
                         * the exception handler (e.g., WITH_EXCEPT_START handler code,
                         * RETURN_VALUE) would be incorrectly placed inside BLK_EXCEPT. */
                        if (mod->verCompare(3, 10) < 0) {
                            stack_hist.push(stack);
                            PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                            except->init();
                            blocks.push(except);
                            curblock = blocks.top();
                        }
                    } else if (tmp->blktype() == ASTBlock::BLK_EXCEPT && cont->hasExcept()) {
                        /* POP_BLOCK popped BLK_EXCEPT -- the try/except structure is
                         * complete.  Close the BLK_CONTAINER so that code following
                         * the except handler (e.g. WITH_EXCEPT_START cleanup for a
                         * containing with-block) doesn't get swallowed inside it and
                         * rendered as a second spurious except: clause. */
                        blocks.pop();
                        if (!blocks.empty()) {
                            curblock = blocks.top();
                            curblock->append(cont.cast<ASTNode>());
                        } else {
                            curblock = defblock;
                            blocks.push(defblock);
                            defblock->append(cont.cast<ASTNode>());
                        }
                    } else if ((tmp->blktype() == ASTBlock::BLK_ELSE && cont->hasFinally())
                            || (tmp->blktype() == ASTBlock::BLK_TRY && !cont->hasExcept())) {
                        stack_hist.push(stack);
                        PycRef<ASTBlock> final = new ASTBlock(ASTBlock::BLK_FINALLY, 0, true);
                        blocks.push(final);
                        curblock = blocks.top();
                    }
                }

                if ((curblock->blktype() == ASTBlock::BLK_FOR || curblock->blktype() == ASTBlock::BLK_ASYNCFOR)
                        && curblock->end() == pos) {
                    blocks.pop();
                    blocks.top()->append(curblock.cast<ASTNode>());
                    curblock = blocks.top();
                }
            }
            break;
        case Pyc::POP_EXCEPT:
            /* Python 3.10+: POP_EXCEPT is a value stack operation that
             * pops exception info. It does NOT close blocks. In Python 3.10,
             * block closing for try/except/finally structures is handled
             * by POP_BLOCK, RERAISE, and other opcodes. */
            if (curblock->blktype() == ASTBlock::BLK_EXCEPT && blocks.size() > 1) {
                PycRef<ASTBlock> except = curblock;
                blocks.pop();
                curblock = blocks.top();
                curblock->append(except.cast<ASTNode>());
                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                }
                /* POP_EXCEPT closes the BLK_EXCEPT; if the parent
                 * is BLK_CONTAINER with hasExcept, close the container
                 * too since the try/except structure is complete. */
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                        && curblock.cast<ASTContainerBlock>()->hasExcept()
                        && blocks.size() > 1) {
                    PycRef<ASTBlock> cont = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(cont.cast<ASTNode>());
                }
            }
            break;
        case Pyc::PUSH_EXC_INFO:
            /* Python 3.11+: pushes exception info tuple. We ignore here to keep decompilation going. */
            break;
        case Pyc::CHECK_EXC_MATCH:
            {
                /* Python 3.11+: compares exception against handler type. */
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                stack.push(new ASTCompare(left, right, ASTCompare::CMP_EXCEPTION));
            }
            break;
        case Pyc::END_FOR:
            {
                stack.pop();

                if ((opcode == Pyc::END_FOR) && (mod->majorVer() == 3) && (mod->minorVer() == 12)) {
                    // one additional pop for python 3.12
                    stack.pop();
                }

                // end for loop here
                /* TODO : Ensure that FOR loop ends here. 
                   Due to CACHE instructions at play, the end indicated in
                   the for loop by pycdas is not correct, it is off by
                   some small amount. */
                if (curblock->blktype() == ASTBlock::BLK_FOR) {
                    PycRef<ASTBlock> prev = blocks.top();
                    blocks.pop();

                    curblock = blocks.top();
                    curblock->append(prev.cast<ASTNode>());
                }
                else {
                    fprintf(stderr, "Wrong block type %i for END_FOR\n", curblock->blktype());
                }
            }
            break;
        case Pyc::POP_TOP:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                if (!curblock->inited()) {
                    if (curblock->blktype() == ASTBlock::BLK_WITH) {
                        curblock.cast<ASTWithBlock>()->setExpr(value);
                    } else {
                        curblock->init();
                    }
                    break;
                } else if (value == nullptr || value->processed()) {
                    break;
                }

                curblock->append(value);

                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    /* This relies on some really uncertain logic...
                     * If it's a comprehension, the only POP_TOP should be
                     * a call to append the iter to the list.
                     */
                    if (value.type() == ASTNode::NODE_CALL) {
                        auto& pparams = value.cast<ASTCall>()->pparams();
                        if (!pparams.empty()) {
                            PycRef<ASTNode> res = pparams.front();
                            stack.push(new ASTComprehension(res));
                        }
                    }
                }
            }
            break;
        case Pyc::PRINT_ITEM:
            {
                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == nullptr && !printNode->eol())
                    printNode->add(stack.top());
                else
                    curblock->append(new ASTPrint(stack.top()));
                stack.pop();
            }
            break;
        case Pyc::PRINT_ITEM_TO:
            {
                PycRef<ASTNode> stream = stack.top();
                stack.pop();

                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == stream && !printNode->eol())
                    printNode->add(stack.top());
                else
                    curblock->append(new ASTPrint(stack.top(), stream));
                stack.pop();
                if (stream)
                    stream->setProcessed();
            }
            break;
        case Pyc::PRINT_NEWLINE:
            {
                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == nullptr && !printNode->eol())
                    printNode->setEol(true);
                else
                    curblock->append(new ASTPrint(nullptr));
                stack.pop();
            }
            break;
        case Pyc::PRINT_NEWLINE_TO:
            {
                PycRef<ASTNode> stream = stack.top();
                stack.pop();

                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == stream && !printNode->eol())
                    printNode->setEol(true);
                else
                    curblock->append(new ASTPrint(nullptr, stream));
                stack.pop();
                if (stream)
                    stream->setProcessed();
            }
            break;
        case Pyc::RAISE_VARARGS_A:
            {
                ASTRaise::param_t paramList;
                for (int i = 0; i < operand; i++) {
                    paramList.push_front(stack.top());
                    stack.pop();
                }
                curblock->append(new ASTRaise(paramList));

                if ((curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                        && stack_hist.size()
                        && (mod->verCompare(2, 6) >= 0)) {
                    stack = stack_hist.top();
                    stack_hist.pop();

                    PycRef<ASTBlock> prev = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(prev.cast<ASTNode>());
                }
            }
            break;
        case Pyc::RERAISE:
        case Pyc::RERAISE_A:
            /* Python 3.10+: RERAISE marks the end of a finally handler
             * (RERAISE 1, re-raise with traceback) or an except handler's
             * unmatched re-raise (RERAISE 0). Close the corresponding
             * block and its parent container. */
            if (mod->verCompare(3, 10) >= 0) {
                /* Handle BLK_FINALLY: close it and its parent BLK_CONTAINER */
                if (curblock->blktype() == ASTBlock::BLK_FINALLY && blocks.size() > 1) {
                    PycRef<ASTBlock> final = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(final.cast<ASTNode>());
                    /* Close the parent BLK_CONTAINER (no except, try/finally) */
                    if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                            && !curblock.cast<ASTContainerBlock>()->hasExcept()
                            && blocks.size() > 1) {
                        PycRef<ASTBlock> cont = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());
                    }
                }
                /* Handle BLK_EXCEPT: close it and parent BLK_CONTAINER (has except) */
                if (curblock->blktype() == ASTBlock::BLK_EXCEPT && blocks.size() > 1) {
                    PycRef<ASTBlock> except = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(except.cast<ASTNode>());
                    if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                            && curblock.cast<ASTContainerBlock>()->hasExcept()
                            && blocks.size() > 1) {
                        PycRef<ASTBlock> cont = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());
                    }
                }
            }
            break;
        case Pyc::RETURN_VALUE:
        case Pyc::INSTRUMENTED_RETURN_VALUE_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                /* At module level, RETURN_VALUE should not occur in correct
                 * bytecode; it is a sign of corrupted block handling (e.g. a
                 * function's return leaked to module level). Suppress the
                 * ASTReturn to avoid SyntaxError: 'return' outside function.
                 *
                 * Similarly, class body code objects (Python 3.10+) do NOT
                 * have the CO_OPTIMIZED flag, unlike function bodies which
                 * always have it.  Suppress RETURN_VALUE in class bodies to
                 * avoid SyntaxError from internal implementation details like
                 * the LOAD_CLOSURE __class__; DUP_TOP; STORE_NAME __classcell__;
                 * RETURN_VALUE sequence at the end of class definitions. */
                if (strcmp(code->name()->value(), "<module>") != 0) {
                    bool is_class = (code->flags() & PycCode::CO_OPTIMIZED) == 0;
                    if (!is_class)
                        curblock->append(new ASTReturn(value));
                }

                if ((curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                        && stack_hist.size()
                        && (mod->verCompare(2, 6) >= 0)) {
                    stack = stack_hist.top();
                    stack_hist.pop();

                    PycRef<ASTBlock> prev = curblock;
                    blocks.pop();

                    if (!blocks.empty()) {
                        curblock = blocks.top();
                        curblock->append(prev.cast<ASTNode>());
                    } else {
                        curblock = defblock;
                        blocks.push(defblock);
                        defblock->append(prev.cast<ASTNode>());
                    }

                    /* In lambdas, ternary true branch may end with RETURN_VALUE
                     * instead of JUMP_FORWARD (Python 3.10+ compiler optimization).
                     * We need to manually create BLK_ELSE here so that the else
                     * branch code becomes its child, allowing CheckIfExpr to
                     * detect the IF+ELSE pair and generate ASTTernary during
                     * cleanup. */
                    if (prev->blktype() == ASTBlock::BLK_IF
                            && inLambda
                            && (mod->verCompare(3, 10) >= 0)) {
                        PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, 0);
                        blocks.push(elseblk);
                        curblock = blocks.top();
                    }
                }
            }
            break;
        case Pyc::RETURN_CONST_A:
        case Pyc::INSTRUMENTED_RETURN_CONST_A:
            {
                PycRef<ASTObject> value = new ASTObject(code->getConst(operand));
                /* Same module-level check as RETURN_VALUE */
                if (strcmp(code->name()->value(), "<module>") != 0)
                    curblock->append(new ASTReturn(value.cast<ASTNode>()));
            }
            break;
        case Pyc::ROT_TWO:
            {
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> two = stack.top();
                stack.pop();

                stack.push(one);
                stack.push(two);
            }
            break;
        case Pyc::ROT_THREE:
            {
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                PycRef<ASTNode> two = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> three = stack.top();
                stack.pop();
                stack.push(one);
                stack.push(three);
                stack.push(two);
            }
            break;
        case Pyc::ROT_FOUR:
            {
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                PycRef<ASTNode> two = stack.top();
                stack.pop();
                PycRef<ASTNode> three = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> four = stack.top();
                stack.pop();
                stack.push(one);
                stack.push(four);
                stack.push(three);
                stack.push(two);
            }
            break;
        case Pyc::SET_LINENO_A:
            // Ignore
            break;
        case Pyc::SETUP_WITH_A:
            {
                int target = pos + operand;
                if (mod->verCompare(3, 10) >= 0)
                    target = pos + operand * sizeof(uint16_t);
                PycRef<ASTBlock> withblock = new ASTWithBlock(target);
                blocks.push(withblock);
                curblock = blocks.top();
            }
            break;
        case Pyc::WITH_EXCEPT_START:
            {
                if (mod->verCompare(3, 11) >= 0)
                    break;
                /* Pop 3 exception info items to maintain stack balance. */
                stack.pop(); stack.pop(); stack.pop();
                if (curblock->blktype() == ASTBlock::BLK_WITH
                        && curblock->end() == curpos) {
                    /* BLK_WITH still open -- exception path during with body.
                     * Close BLK_WITH and restore stack_hist for exception handling. */
                    PycRef<ASTBlock> with = curblock;
                    blocks.pop();
                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    }
                    curblock = blocks.top();
                    curblock->append(with.cast<ASTNode>());
                } else if (mod->verCompare(3, 10) >= 0) {
                    /* Python 3.10+: BLK_WITH already closed by POP_BLOCK on the
                     * normal path. */
                    if (curblock->blktype() == ASTBlock::BLK_TRY) {
                        /* POP_BLOCK's BLK_TRY pop was deferred so that continuation
                         * code (e.g. RETURN_VALUE) stays inside the try body on the
                         * normal path. Now at WITH_EXCEPT_START (the exception path),
                         * close BLK_TRY without restoring stack_hist (it was saved
                         * at need_try for the exception handler path). */
                        PycRef<ASTBlock> tryblk = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(tryblk.cast<ASTNode>());
                        /* Fall through to skip past the handler code */
                    }
                    if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                        /* Skip past the WITH_EXCEPT_START handler code to the
                         * SETUP_FINALLY target in the BLK_CONTAINER, which is
                         * the exception handler entry (DUP_TOP for try/except).
                         * Note: `pos` in SETUP_FINALLY handler has already been
                         * advanced by bc_next(), so curblock->end() correctly
                         * points to the handler entry offset. */
                        int target = curblock->end();
                        int skip = target - pos;
                        if (skip > 0) {
                            source.skipBytes(skip);
                            pos = target;
                        }
                    }
                }
            }
            break;
        case Pyc::BEFORE_WITH:
            /* Python 3.11: setup for with block; ignore. */
            break;
        case Pyc::BEFORE_ASYNC_WITH:
            /* Setup for async with; ignore, handled by SETUP_ASYNC_WITH. */
            break;
        case Pyc::SETUP_ASYNC_WITH_A:
            {
                int target = pos + operand;
                if (mod->verCompare(3, 10) >= 0)
                    target = pos + operand * sizeof(uint16_t);
                PycRef<ASTBlock> withblock = new ASTWithBlock(target);
                withblock.cast<ASTWithBlock>()->setAsync(true);
                blocks.push(withblock);
                curblock = blocks.top();
            }
            break;
        case Pyc::END_ASYNC_FOR:
        case Pyc::WITH_CLEANUP:
        case Pyc::WITH_CLEANUP_START:
            {
                // Stack top should be a None. Ignore it.
                PycRef<ASTNode> none = stack.top();
                stack.pop();

                if (none != NULL) {
                    fprintf(stderr, "Something TERRIBLE happened!\n");
                    break;
                }

                if (curblock->blktype() == ASTBlock::BLK_WITH
                        && curblock->end() == curpos) {
                    PycRef<ASTBlock> with = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(with.cast<ASTNode>());
                }
                else {
                    fprintf(stderr, "Something TERRIBLE happened! No matching with block found for WITH_CLEANUP at %d\n", curpos);
                }
            }
            break;
        case Pyc::WITH_CLEANUP_FINISH:
            /* Ignore this */
            break;
        case Pyc::SETUP_EXCEPT_A:
            {
                int target = pos + operand;
                if (mod->verCompare(3, 10) >= 0)
                    target = pos + operand * sizeof(uint16_t);
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    curblock.cast<ASTContainerBlock>()->setExcept(target);
                } else {
                    PycRef<ASTBlock> next = new ASTContainerBlock(0, target);
                    blocks.push(next.cast<ASTBlock>());
                }

                /* Store the current stack for the except/finally statement(s) */
                stack_hist.push(stack);
                PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, target, true);
                blocks.push(tryblock.cast<ASTBlock>());
                curblock = blocks.top();

                need_try = false;
            }
            break;
        case Pyc::SETUP_FINALLY_A:
            {
                int target = pos + operand;
                if (mod->verCompare(3, 10) >= 0)
                    target = pos + operand * sizeof(uint16_t);
                PycRef<ASTBlock> next = new ASTContainerBlock(target);
                blocks.push(next.cast<ASTBlock>());
                curblock = blocks.top();

                need_try = true;

                /* Python 3.10: SETUP_FINALLY is used for both try/except AND try/finally.
                 * Pre-scan the handler target bytecode to distinguish them.
                 * If the handler starts with DUP_TOP (followed by exception type check),
                 * it's try/except. Otherwise it's try/finally.
                 *
                 * Note: In the SETUP_FINALLY handler, `pos` has already been advanced
                 * by bc_next() (pos = start_of_instruction + 2), so the target
                 * formula `pos + operand * sizeof(uint16_t)` already yields the
                 * correct handler entry offset. */
                if (mod->verCompare(3, 10) >= 0) {
                    PycBuffer scan(code->code()->value(), code->code()->length());
                    for (int i = 0; i < target; i++)
                        (void)scan.getByte();
                    int h_op = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(), scan.getByte());
                    if (h_op == Pyc::DUP_TOP) {
                        /* try/except pattern: handler starts with DUP_TOP + JUMP_IF_NOT_EXC_MATCH.
                         * Clear m_finally since this is NOT a finally handler. */
                        next.cast<ASTContainerBlock>()->setExcept(target);
                        next.cast<ASTContainerBlock>()->setFinally(0);
                    }
                }
            }
            break;
        case Pyc::SETUP_LOOP_A:
            {
                PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_WHILE, pos+operand, NULL, false);
                blocks.push(next.cast<ASTBlock>());
                curblock = blocks.top();
            }
            break;
        case Pyc::SLICE_0:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE0);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_1:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE1, lower);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_2:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE2, NULL, upper);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_3:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE3, lower, upper);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::STORE_ATTR_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = stack.top();
                    stack.pop();
                    PycRef<ASTNode> attr = new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(attr);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();
                        if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> name = stack.top();
                    stack.pop();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> attr = new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR);
                    if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, attr, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, attr));
                    }
                }
            }
            break;
        case Pyc::STORE_DEREF_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = new ASTName(code->getCellVar(mod, operand));

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> name = new ASTName(code->getCellVar(mod, operand));

                    if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, name));
                    }
                }
            }
            break;
        case Pyc::STORE_FAST_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name;

                    if (mod->verCompare(1, 3) < 0)
                        name = new ASTName(code->getName(operand));
                    else
                        name = new ASTName(code->getLocal(operand));

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> name;

                    if (mod->verCompare(1, 3) < 0)
                        name = new ASTName(code->getName(operand));
                    else
                        name = new ASTName(code->getLocal(operand));

                    if (name.cast<ASTName>()->name()->value()[0] == '_'
                            && name.cast<ASTName>()->name()->value()[1] == '[') {
                        /* Don't show stores of list comp append objects. */
                        break;
                    }

                    if (curblock->blktype() == ASTBlock::BLK_FOR
                            && !curblock->inited()) {
                        curblock.cast<ASTIterBlock>()->setIndex(name);
                    } else if (curblock->blktype() == ASTBlock::BLK_WITH
                                   && !curblock->inited()) {
                        curblock.cast<ASTWithBlock>()->setExpr(value);
                        curblock.cast<ASTWithBlock>()->setVar(name);
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, name));
                    }
                }
            }
            break;
        case Pyc::STORE_GLOBAL_A:
            {
                PycRef<ASTNode> name = new ASTName(code->getName(operand));

                if (unpack) {
                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, name));
                    }
                }

                /* Mark the global as used */
                code->markGlobal(name.cast<ASTName>()->name());
            }
            break;
        case Pyc::STORE_NAME_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = new ASTName(code->getName(operand));

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();

                    PycRef<PycString> varname = code->getName(operand);
                    if (varname->length() >= 2 && varname->value()[0] == '_'
                            && varname->value()[1] == '[') {
                        /* Don't show stores of list comp append objects. */
                        break;
                    }
                    if (strcmp(varname->value(), "__classcell__") == 0) {
                        /* __classcell__ is an internal implementation detail at
                         * the end of a class body, used by super().  The value
                         * was already consumed from the stack above; suppress
                         * the assignment to avoid invalid syntax at module level. */
                        break;
                    }

                    // Return private names back to their original name
                    const std::string class_prefix = std::string("_") + code->name()->strValue();
                    if (varname->startsWith(class_prefix + std::string("__")))
                        varname->setValue(varname->strValue().substr(class_prefix.size()));

                    PycRef<ASTNode> name = new ASTName(varname);

                    if (curblock->blktype() == ASTBlock::BLK_FOR
                            && !curblock->inited()) {
                        curblock.cast<ASTIterBlock>()->setIndex(name);
                    } else if (stack.top().type() == ASTNode::NODE_IMPORT) {
                        PycRef<ASTImport> import = stack.top().cast<ASTImport>();

                        import->add_store(new ASTStore(value, name));
                    } else if (curblock->blktype() == ASTBlock::BLK_WITH
                               && !curblock->inited()) {
                        curblock.cast<ASTWithBlock>()->setExpr(value);
                        curblock.cast<ASTWithBlock>()->setVar(name);
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, name));

                        if (value.type() == ASTNode::NODE_INVALID)
                            break;
                    }
                }
            }
            break;
        case Pyc::STORE_SLICE_0:
            {
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE0))));
            }
            break;
        case Pyc::STORE_SLICE_1:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE1, upper))));
            }
            break;
        case Pyc::STORE_SLICE_2:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE2, NULL, lower))));
            }
            break;
        case Pyc::STORE_SLICE_3:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE3, upper, lower))));
            }
            break;
        case Pyc::STORE_SUBSCR:
            {
                if (unpack) {
                    PycRef<ASTNode> subscr = stack.top();
                    stack.pop();
                    PycRef<ASTNode> dest = stack.top();
                    stack.pop();

                    PycRef<ASTNode> save = new ASTSubscr(dest, subscr);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(save);
                    else
                        fputs("Something TERRIBLE happened!\n", stderr);

                    if (--unpack <= 0) {
                        stack.pop();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();
                        if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> subscr = stack.top();
                    stack.pop();
                    PycRef<ASTNode> dest = stack.top();
                    stack.pop();
                    PycRef<ASTNode> src = stack.top();
                    stack.pop();

                    // If variable annotations are enabled, we'll need to check for them here.
                    // Python handles a varaible annotation by setting:
                    // __annotations__['var-name'] = type
                    const bool found_annotated_var = (variable_annotations && dest->type() == ASTNode::Type::NODE_NAME
                                                      && dest.cast<ASTName>()->name()->isEqual("__annotations__"));

                    if (found_annotated_var) {
                        // Annotations can be done alone or as part of an assignment.
                        // In the case of an assignment, we'll see a NODE_STORE on the stack.
                        if (!curblock->nodes().empty() && curblock->nodes().back()->type() == ASTNode::Type::NODE_STORE) {
                            // Replace the existing NODE_STORE with a new one that includes the annotation.
                            PycRef<ASTStore> store = curblock->nodes().back().cast<ASTStore>();
                            curblock->removeLast();
                            curblock->append(new ASTStore(store->src(),
                                                          new ASTAnnotatedVar(subscr, src)));
                        } else {
                            curblock->append(new ASTAnnotatedVar(subscr, src));
                        }
                    } else {
                        if (dest.type() == ASTNode::NODE_MAP) {
                            dest.cast<ASTMap>()->add(subscr, src);
                        } else if (src.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(src, new ASTSubscr(dest, subscr), stack, curblock);
                        } else {
                            curblock->append(new ASTStore(src, new ASTSubscr(dest, subscr)));
                        }
                    }
                }
            }
            break;
        case Pyc::UNARY_CALL:
            {
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                stack.push(new ASTCall(func, ASTCall::pparam_t(), ASTCall::kwparam_t()));
            }
            break;
        case Pyc::UNARY_CONVERT:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTConvert(name));
            }
            break;
        case Pyc::UNARY_INVERT:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_INVERT));
            }
            break;
        case Pyc::UNARY_NEGATIVE:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_NEGATIVE));
            }
            break;
        case Pyc::UNARY_NOT:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_NOT));
            }
            break;
        case Pyc::UNARY_POSITIVE:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_POSITIVE));
            }
            break;
        case Pyc::UNPACK_LIST_A:
        case Pyc::UNPACK_TUPLE_A:
        case Pyc::UNPACK_SEQUENCE_A:
            {
                unpack = operand;
                if (unpack > 0) {
                    ASTTuple::value_t vals;
                    stack.push(new ASTTuple(vals));
                } else {
                    // Unpack zero values and assign it to top of stack or for loop variable.
                    // E.g. [] = TOS / for [] in X
                    ASTTuple::value_t vals;
                    auto tup = new ASTTuple(vals);
                    if (curblock->blktype() == ASTBlock::BLK_FOR
                        && !curblock->inited()) {
                        tup->setRequireParens(true);
                        curblock.cast<ASTIterBlock>()->setIndex(tup);
                    } else if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                        auto chainStore = stack.top();
                        stack.pop();
                        append_to_chain_store(chainStore, tup, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(stack.top(), tup));
                        stack.pop();
                    }
                }
            }
            break;
        case Pyc::UNPACK_EX_A:
            {
                int prefix = operand & 0xFF;
                int suffix = (operand >> 8) & 0xFF;
                unpack = prefix + 1 + suffix;  // +1 for the starred list
                if (unpack > 0) {
                    ASTTuple::value_t vals;
                    stack.push(new ASTTuple(vals));
                }
            }
            break;
        case Pyc::YIELD_FROM:
            {
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                // TODO: Support yielding into a non-null destination
                PycRef<ASTNode> value = stack.top();
                if (value) {
                    value->setProcessed();
                    curblock->append(new ASTReturn(value, ASTReturn::YIELD_FROM));
                }
            }
            break;
        case Pyc::YIELD_VALUE:
        case Pyc::INSTRUMENTED_YIELD_VALUE_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                curblock->append(new ASTReturn(value, ASTReturn::YIELD));
            }
            break;
        case Pyc::SETUP_ANNOTATIONS:
            variable_annotations = true;
            break;
        case Pyc::PRECALL_A:
        case Pyc::RESUME_A:
        case Pyc::INSTRUMENTED_RESUME_A:
            /* We just entirely ignore this / no-op */
            break;
        case Pyc::CACHE:
            /* These "fake" opcodes are used as placeholders for optimizing
               certain opcodes in Python 3.11+.  Since we have no need for
               that during disassembly/decompilation, we can just treat these
               as no-ops. */
            break;
        case Pyc::PUSH_NULL:
            stack.push(nullptr);
            break;
        case Pyc::GEN_START_A:
            stack.pop();
            break;
        case Pyc::SWAP_A:
            {
                unpack = operand;
                ASTTuple::value_t values;
                ASTTuple::value_t next_tuple;
                values.resize(operand);
                for (int i = 0; i < operand; i++) {
                    values[operand - i - 1] = stack.top();
                    stack.pop();
                }
                auto tup = new ASTTuple(values);
                tup->setRequireParens(false);
                auto next_tup = new ASTTuple(next_tuple);
                next_tup->setRequireParens(false);
                stack.push(tup);
                stack.push(next_tup);
            }
            break;
        case Pyc::BINARY_SLICE:
            {
                PycRef<ASTNode> end = stack.top();
                stack.pop();
                PycRef<ASTNode> start = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();

                if (start.type() == ASTNode::NODE_OBJECT
                        && start.cast<ASTObject>()->object() == Pyc_None) {
                    start = NULL;
                }

                if (end.type() == ASTNode::NODE_OBJECT
                        && end.cast<ASTObject>()->object() == Pyc_None) {
                    end = NULL;
                }

                PycRef<ASTNode> slice;
                if (start == NULL && end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE0);
                } else if (start == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE2, start, end);
                } else if (end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE1, start, end);
                } else {
                    slice = new ASTSlice(ASTSlice::SLICE3, start, end);
                }
                stack.push(new ASTSubscr(dest, slice));
            }
            break;
        case Pyc::STORE_SLICE:
            {
                PycRef<ASTNode> end = stack.top();
                stack.pop();
                PycRef<ASTNode> start = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> values = stack.top();
                stack.pop();

                if (start.type() == ASTNode::NODE_OBJECT
                        && start.cast<ASTObject>()->object() == Pyc_None) {
                    start = NULL;
                }

                if (end.type() == ASTNode::NODE_OBJECT
                        && end.cast<ASTObject>()->object() == Pyc_None) {
                    end = NULL;
                }

                PycRef<ASTNode> slice;
                if (start == NULL && end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE0);
                } else if (start == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE2, start, end);
                } else if (end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE1, start, end);
                } else {
                    slice = new ASTSlice(ASTSlice::SLICE3, start, end);
                }

                curblock->append(new ASTStore(values, new ASTSubscr(dest, slice)));
            }
            break;
        case Pyc::COPY_A:
            {
                PycRef<ASTNode> value = stack.top(operand);
                stack.push(value);
            }
            break;
        case Pyc::JUMP_IF_NOT_EXC_MATCH_A:
            /* JUMP_IF_NOT_EXC_MATCH compares TOS (exception class) with TOS1 (exception instance).
             * If NOT match, jump to target; if match, pop TOS and continue.
             * Here we simulate "match" -- pop TOS (exception class) to maintain stack balance. */
            stack.pop();
            /* Python 3.10+: If curblock is a container with except, this marks the
             * start of a new except clause (multi-except support). */
            if (mod->verCompare(3, 10) >= 0
                    && curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && curblock.cast<ASTContainerBlock>()->hasExcept()) {
                stack_hist.push(stack);
                PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                except->init();
                blocks.push(except);
                curblock = blocks.top();
            }
            break;
        default:
            fprintf(stderr, "Unsupported opcode: %s (%d) at position %d, skipping %d byte(s)\n",
                    Pyc::OpcodeName(opcode), opcode, curpos, pos - curpos);
            unsupportedOpcode = true;
            cleanBuild = false;
            break;
        }

        else_pop =  ( (curblock->blktype() == ASTBlock::BLK_ELSE)
                      || (curblock->blktype() == ASTBlock::BLK_IF)
                      || (curblock->blktype() == ASTBlock::BLK_ELIF) )
                 && (curblock->end() == pos);
    }

    if (stack_hist.size()) {
        fputs("Warning: Stack history is not empty!\n", stderr);

        while (stack_hist.size()) {
            stack_hist.pop();
        }
    }

    if (blocks.size() > 1) {
        fputs("Warning: block stack is not empty!\n", stderr);

        while (blocks.size() > 1) {
            PycRef<ASTBlock> tmp = blocks.top();
            blocks.pop();

            blocks.top()->append(tmp.cast<ASTNode>());
            CheckIfExpr(stack, blocks.top());
        }
    }

    /* In lambdas, expression results (e.g. ASTTernary from CheckIfExpr) end up
     * on the value stack but are not added to defblock's children. Wrap them in
     * ASTReturn so they appear in the decompiled output (the "return" keyword
     * will be omitted by print_src when inLambda is true). */
    if (inLambda && !unsupportedOpcode) {
        while (!stack.empty()) {
            PycRef<ASTNode> expr = stack.top();
            stack.pop();
            defblock->append(new ASTReturn(expr));
        }
    }

    if (!unsupportedOpcode)
        cleanBuild = true;
    return new ASTNodeList(defblock->nodes());
    } catch (const std::bad_cast&) {
        cleanBuild = false;
        fprintf(stderr, "bad_cast in BuildFromCode for %s\n", code->name()->value());
        return new ASTNodeList(ASTNodeList::list_t());
    }
}

static void append_to_chain_store(const PycRef<ASTNode> &chainStore,
        PycRef<ASTNode> item, FastStack& stack, const PycRef<ASTBlock>& curblock)
{
    stack.pop();    // ignore identical source object.
    chainStore.cast<ASTChainStore>()->append(item);
    if (stack.top().type() == PycObject::TYPE_NULL) {
        curblock->append(chainStore);
    } else {
        stack.push(chainStore);
    }
}

static int cmp_prec(PycRef<ASTNode> parent, PycRef<ASTNode> child)
{
    /* Determine whether the parent has higher precedence than therefore
       child, so we don't flood the source code with extraneous parens.
       Else we'd have expressions like (((a + b) + c) + d) when therefore
       equivalent, a + b + c + d would suffice. */

    if (parent.type() == ASTNode::NODE_UNARY && parent.cast<ASTUnary>()->op() == ASTUnary::UN_NOT)
        return 1;   // Always parenthesize not(x)
    if (child.type() == ASTNode::NODE_BINARY) {
        PycRef<ASTBinary> binChild = child.cast<ASTBinary>();
        if (parent.type() == ASTNode::NODE_BINARY) {
            PycRef<ASTBinary> binParent = parent.cast<ASTBinary>();
            if (binParent->right() == child) {
                if (binParent->op() == ASTBinary::BIN_SUBTRACT &&
                    binChild->op() == ASTBinary::BIN_ADD)
                    return 1;
                else if (binParent->op() == ASTBinary::BIN_DIVIDE &&
                         binChild->op() == ASTBinary::BIN_MULTIPLY)
                    return 1;
            }
            return binChild->op() - binParent->op();
        }
        else if (parent.type() == ASTNode::NODE_COMPARE)
            return (binChild->op() == ASTBinary::BIN_LOG_AND ||
                    binChild->op() == ASTBinary::BIN_LOG_OR) ? 1 : -1;
        else if (parent.type() == ASTNode::NODE_UNARY)
            return (binChild->op() == ASTBinary::BIN_POWER) ? -1 : 1;
    } else if (child.type() == ASTNode::NODE_UNARY) {
        PycRef<ASTUnary> unChild = child.cast<ASTUnary>();
        if (parent.type() == ASTNode::NODE_BINARY) {
            PycRef<ASTBinary> binParent = parent.cast<ASTBinary>();
            if (binParent->op() == ASTBinary::BIN_LOG_AND ||
                binParent->op() == ASTBinary::BIN_LOG_OR)
                return -1;
            else if (unChild->op() == ASTUnary::UN_NOT)
                return 1;
            else if (binParent->op() == ASTBinary::BIN_POWER)
                return 1;
            else
                return -1;
        } else if (parent.type() == ASTNode::NODE_COMPARE) {
            return (unChild->op() == ASTUnary::UN_NOT) ? 1 : -1;
        } else if (parent.type() == ASTNode::NODE_UNARY) {
            return unChild->op() - parent.cast<ASTUnary>()->op();
        }
    } else if (child.type() == ASTNode::NODE_COMPARE) {
        PycRef<ASTCompare> cmpChild = child.cast<ASTCompare>();
        if (parent.type() == ASTNode::NODE_BINARY)
            return (parent.cast<ASTBinary>()->op() == ASTBinary::BIN_LOG_AND ||
                    parent.cast<ASTBinary>()->op() == ASTBinary::BIN_LOG_OR) ? -1 : 1;
        else if (parent.type() == ASTNode::NODE_COMPARE)
            return cmpChild->op() - parent.cast<ASTCompare>()->op();
        else if (parent.type() == ASTNode::NODE_UNARY)
            return (parent.cast<ASTUnary>()->op() == ASTUnary::UN_NOT) ? -1 : 1;
    }

    /* For normal nodes, don't parenthesize anything */
    return -1;
}

static void print_ordered(PycRef<ASTNode> parent, PycRef<ASTNode> child,
                          PycModule* mod, std::ostream& pyc_output)
{
    if (child.type() == ASTNode::NODE_BINARY ||
        child.type() == ASTNode::NODE_COMPARE) {
        if (cmp_prec(parent, child) > 0) {
            pyc_output << "(";
            print_src(child, mod, pyc_output);
            pyc_output << ")";
        } else {
            print_src(child, mod, pyc_output);
        }
    } else if (child.type() == ASTNode::NODE_UNARY) {
        if (cmp_prec(parent, child) > 0) {
            pyc_output << "(";
            print_src(child, mod, pyc_output);
            pyc_output << ")";
        } else {
            print_src(child, mod, pyc_output);
        }
    } else {
        print_src(child, mod, pyc_output);
    }
}

static void start_line(int indent, std::ostream& pyc_output)
{
    if (inLambda)
        return;
    for (int i=0; i<indent; i++)
        pyc_output << "    ";
}

static void end_line(std::ostream& pyc_output)
{
    if (inLambda)
        return;
    pyc_output << "\n";
}

int cur_indent = -1;
static void print_block(PycRef<ASTBlock> blk, PycModule* mod,
                        std::ostream& pyc_output)
{
    ASTBlock::list_t lines = blk->nodes();

    if (lines.size() == 0) {
        PycRef<ASTNode> pass = new ASTKeyword(ASTKeyword::KW_PASS);
        start_line(cur_indent, pyc_output);
        print_src(pass, mod, pyc_output);
    }

    for (auto ln = lines.cbegin(); ln != lines.cend();) {
        // In lambda, detect BLK_IF followed by BLK_ELSE and output as ternary expression
        // instead of if/else statement (e.g., "x if cond else y").
        if (inLambda) {
            if ((*ln).cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
                PycRef<ASTBlock> childBlk = (*ln).cast<ASTBlock>();
                if (childBlk->blktype() == ASTBlock::BLK_IF) {
                    auto next = ln;
                    ++next;
                    if (next != lines.end() && (*next).cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
                        PycRef<ASTBlock> nextBlk = (*next).cast<ASTBlock>();
                        if (nextBlk->blktype() == ASTBlock::BLK_ELSE) {
                            // Output ternary: <then_expr> if <cond> else <else_expr>
                            PycRef<ASTCondBlock> ifBlock = childBlk.cast<ASTCondBlock>();
                            PycRef<ASTCondBlock> elseBlock = nextBlk.cast<ASTCondBlock>();
                            print_block(ifBlock.cast<ASTBlock>(), mod, pyc_output);
                            pyc_output << " if ";
                            print_src(ifBlock->cond(), mod, pyc_output);
                            pyc_output << " else ";
                            print_block(elseBlock.cast<ASTBlock>(), mod, pyc_output);
                            // Skip both BLK_IF and BLK_ELSE
                            ++ln;
                            ++ln;
                            if (ln != lines.end()) {
                                end_line(pyc_output);
                            }
                            continue;
                        }
                    }
                }
            }
        }

        if ((*ln).cast<ASTNode>().type() != ASTNode::NODE_NODELIST) {
            start_line(cur_indent, pyc_output);
        }

        // Detect orphaned BLK_TRY blocks that lack a matching BLK_EXCEPT or BLK_FINALLY.
        // This can happen when BLK_MAIN flattening (from POP_BLOCK) separates the try
        // from its except/finally siblings.
        bool orphanTry = false;
        if ((*ln).cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
            PycRef<ASTBlock> childBlk = (*ln).cast<ASTBlock>();
            if (childBlk->blktype() == ASTBlock::BLK_TRY) {
                orphanTry = true;
                for (auto next = ln; ++next != lines.end(); ) {
                    if (next->cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
                        PycRef<ASTBlock> nextBlk = next->cast<ASTBlock>();
                        if (nextBlk->blktype() == ASTBlock::BLK_EXCEPT
                                || nextBlk->blktype() == ASTBlock::BLK_FINALLY) {
                            orphanTry = false;
                            break;
                        }
                    }
                }
            }
        }

        print_src(*ln, mod, pyc_output);

        // If the try block has no matching except/finally, add a dummy except: pass
        // to produce valid Python syntax.
        if (orphanTry) {
            end_line(pyc_output);
            start_line(cur_indent, pyc_output);
            pyc_output << "except:\n";
            cur_indent++;
            start_line(cur_indent, pyc_output);
            pyc_output << "pass";
            cur_indent--;
        }

        if (++ln != lines.end()) {
            end_line(pyc_output);
        }
    }
}

void print_formatted_value(PycRef<ASTFormattedValue> formatted_value, PycModule* mod,
                           std::ostream& pyc_output)
{
    pyc_output << "{";
    print_src(formatted_value->val(), mod, pyc_output);

    switch (formatted_value->conversion() & ASTFormattedValue::CONVERSION_MASK) {
    case ASTFormattedValue::NONE:
        break;
    case ASTFormattedValue::STR:
        pyc_output << "!s";
        break;
    case ASTFormattedValue::REPR:
        pyc_output << "!r";
        break;
    case ASTFormattedValue::ASCII:
        pyc_output << "!a";
        break;
    }
    if (formatted_value->conversion() & ASTFormattedValue::HAVE_FMT_SPEC) {
        pyc_output << ":" << formatted_value->format_spec().cast<ASTObject>()->object().cast<PycString>()->value();
    }
    pyc_output << "}";
}

static std::unordered_set<ASTNode *> node_seen;

void print_src(PycRef<ASTNode> node, PycModule* mod, std::ostream& pyc_output)
{
    if (node == NULL) {
        pyc_output << "None";
        cleanBuild = true;
        return;
    }

    if (node_seen.find((ASTNode *)node) != node_seen.end()) {
        fputs("WARNING: Circular reference detected\n", stderr);
        return;
    }
    node_seen.insert((ASTNode *)node);

    try {
    switch (node->type()) {
    case ASTNode::NODE_BINARY:
    case ASTNode::NODE_COMPARE:
        {
            PycRef<ASTBinary> bin = node.cast<ASTBinary>();
            print_ordered(node, bin->left(), mod, pyc_output);
            pyc_output << bin->op_str();
            print_ordered(node, bin->right(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_UNARY:
        {
            PycRef<ASTUnary> un = node.cast<ASTUnary>();
            pyc_output << un->op_str();
            print_ordered(node, un->operand(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_CALL:
        {
            PycRef<ASTCall> call = node.cast<ASTCall>();

            // Detect comprehension pattern: comp_func(iterable)
            if (call->func().type() == ASTNode::NODE_FUNCTION
                && call->pparams().size() == 1
                && call->kwparams().empty()
                && !call->hasVar() && !call->hasKW()) {
                PycRef<ASTFunction> comp_func = call->func().cast<ASTFunction>();
                PycRef<ASTNode> comp_code_node = comp_func->code();
                PycRef<PycCode> comp_code;
                if (comp_code_node.type() == ASTNode::NODE_OBJECT) {
                    comp_code = comp_code_node.cast<ASTObject>()->object().try_cast<PycCode>();
                }
                if (comp_code) {
                    const char* cname = comp_code->name()->value();
                    int comp_type = 0;
                    if (strcmp(cname, "<listcomp>") == 0) comp_type = 1;
                    else if (strcmp(cname, "<setcomp>") == 0) comp_type = 2;
                    else if (strcmp(cname, "<dictcomp>") == 0) comp_type = 3;
                    else if (strcmp(cname, "<genexpr>") == 0) comp_type = 4;

                    if (comp_type != 0) {
                        PycRef<ASTNode> iterable = call->pparams().front();
                        // We can't recursively BuildFromCode (global state corruption).
                        // Instead, output the inner code as a decompiled block
                        // and format it as a comprehension.
                        // For now, output a simplified but syntactically valid form.
                        if (comp_type == 1) pyc_output << "[";
                        else if (comp_type == 2) pyc_output << "{";
                        else if (comp_type == 3) pyc_output << "{";
                        else pyc_output << "(";

                        // Decompile the inner code to a string, then extract comp pattern
                        // Save global state
                        bool savedCleanBuild = cleanBuild;
                        bool savedInLambda = inLambda;
                        int savedIndent = cur_indent;
                        std::unordered_set<ASTNode*> savedNodeSeen = node_seen;

                        cleanBuild = true;
                        inLambda = false;
                        cur_indent = -1;
                        node_seen.clear();

                        PycRef<ASTNode> inner_ast = BuildFromCode(comp_code, mod);
                        PycRef<ASTNodeList> inner_list = inner_ast.try_cast<ASTNodeList>();
                        if (!inner_list) {
                            inner_list = new ASTNodeList(ASTNodeList::list_t());
                            inner_list->append(inner_ast);
                        }

                        // Find NODE_COMPREHENSION in inner AST
                        bool found_comp = false;
                        for (const auto& inner_node : inner_list->nodes()) {
                            if (inner_node.type() == ASTNode::NODE_STORE) {
                                PycRef<ASTNode> src = inner_node.cast<ASTStore>()->src();
                                if (src.type() == ASTNode::NODE_COMPREHENSION) {
                                    PycRef<ASTComprehension> comp = src.cast<ASTComprehension>();
                                    print_src(comp->result(), mod, pyc_output);
                                    for (const auto& gen : comp->generators()) {
                                        pyc_output << " for ";
                                        print_src(gen->index(), mod, pyc_output);
                                        pyc_output << " in ";
                                        if (!found_comp) {
                                            print_src(iterable, mod, pyc_output);
                                        } else {
                                            print_src(gen->iter(), mod, pyc_output);
                                        }
                                        if (gen->condition()) {
                                            pyc_output << " if ";
                                            print_src(gen->condition(), mod, pyc_output);
                                        }
                                        found_comp = true;
                                    }
                                    found_comp = true;
                                    break;
                                }
                            }
                        }

                        // Restore global state
                        cleanBuild = savedCleanBuild;
                        inLambda = savedInLambda;
                        cur_indent = savedIndent;
                        node_seen = savedNodeSeen;

                        if (!found_comp) {
                            pyc_output << "x for x in ";
                            print_src(iterable, mod, pyc_output);
                            cleanBuild = false;
                        }

                        if (comp_type == 1) pyc_output << "]";
                        else if (comp_type == 2) pyc_output << "}";
                        else if (comp_type == 3) pyc_output << "}";
                        else pyc_output << ")";
                        break;
                    }
                }
            }

            print_src(call->func(), mod, pyc_output);
            pyc_output << "(";
            bool first = true;
            for (const auto& param : call->pparams()) {
                if (!first)
                    pyc_output << ", ";
                print_src(param, mod, pyc_output);
                first = false;
            }
            for (const auto& param : call->kwparams()) {
                if (!first)
                    pyc_output << ", ";
                if (param.first.type() == ASTNode::NODE_NAME) {
                    pyc_output << param.first.cast<ASTName>()->name()->value() << " = ";
                } else {
                    PycRef<PycString> str_name = param.first.cast<ASTObject>()->object().cast<PycString>();
                    pyc_output << str_name->value() << " = ";
                }
                print_src(param.second, mod, pyc_output);
                first = false;
            }
            if (call->hasVar()) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << "*";
                print_src(call->var(), mod, pyc_output);
                first = false;
            }
            if (call->hasKW()) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << "**";
                print_src(call->kw(), mod, pyc_output);
                first = false;
            }
            pyc_output << ")";
        }
        break;
    case ASTNode::NODE_DELETE:
        {
            pyc_output << "del ";
            print_src(node.cast<ASTDelete>()->value(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_EXEC:
        {
            PycRef<ASTExec> exec = node.cast<ASTExec>();
            pyc_output << "exec ";
            print_src(exec->statement(), mod, pyc_output);

            if (exec->globals() != NULL) {
                pyc_output << " in ";
                print_src(exec->globals(), mod, pyc_output);

                if (exec->locals() != NULL
                        && exec->globals() != exec->locals()) {
                    pyc_output << ", ";
                    print_src(exec->locals(), mod, pyc_output);
                }
            }
        }
        break;
    case ASTNode::NODE_FORMATTEDVALUE:
        pyc_output << "f" F_STRING_QUOTE;
        print_formatted_value(node.cast<ASTFormattedValue>(), mod, pyc_output);
        pyc_output << F_STRING_QUOTE;
        break;
    case ASTNode::NODE_JOINEDSTR:
        pyc_output << "f" F_STRING_QUOTE;
        for (const auto& val : node.cast<ASTJoinedStr>()->values()) {
            switch (val.type()) {
            case ASTNode::NODE_FORMATTEDVALUE:
                print_formatted_value(val.cast<ASTFormattedValue>(), mod, pyc_output);
                break;
            case ASTNode::NODE_OBJECT:
                // When printing a piece of the f-string, keep the quote style consistent.
                // This avoids problems when ''' or """ is part of the string.
                print_const(pyc_output, val.cast<ASTObject>()->object(), mod, F_STRING_QUOTE);
                break;
            default:
                fprintf(stderr, "Unsupported node type %d in NODE_JOINEDSTR\n", val.type());
            }
        }
        pyc_output << F_STRING_QUOTE;
        break;
    case ASTNode::NODE_KEYWORD:
        pyc_output << node.cast<ASTKeyword>()->word_str();
        break;
    case ASTNode::NODE_LIST:
        {
            pyc_output << "[";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTList>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                print_src(val, mod, pyc_output);
                first = false;
            }
            cur_indent--;
            pyc_output << "]";
        }
        break;
    case ASTNode::NODE_SET:
        {
            pyc_output << "{";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTSet>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                print_src(val, mod, pyc_output);
                first = false;
            }
            cur_indent--;
            pyc_output << "}";
        }
        break;
    case ASTNode::NODE_COMPREHENSION:
        {
            PycRef<ASTComprehension> comp = node.cast<ASTComprehension>();

            pyc_output << "[ ";
            print_src(comp->result(), mod, pyc_output);

            for (const auto& gen : comp->generators()) {
                pyc_output << " for ";
                print_src(gen->index(), mod, pyc_output);
                pyc_output << " in ";
                print_src(gen->iter(), mod, pyc_output);
                if (gen->condition()) {
                    pyc_output << " if ";
                    print_src(gen->condition(), mod, pyc_output);
                }
            }
            pyc_output << " ]";
        }
        break;
    case ASTNode::NODE_MAP:
        {
            pyc_output << "{";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTMap>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                print_src(val.first, mod, pyc_output);
                pyc_output << ": ";
                print_src(val.second, mod, pyc_output);
                first = false;
            }
            cur_indent--;
            pyc_output << " }";
        }
        break;
    case ASTNode::NODE_CONST_MAP:
        {
            PycRef<ASTConstMap> const_map = node.cast<ASTConstMap>();
            PycTuple::value_t keys = const_map->keys().cast<ASTObject>()->object().cast<PycTuple>()->values();
            ASTConstMap::values_t values = const_map->values();

            auto map = new ASTMap;
            for (const auto& key : keys) {
                // Values are pushed onto the stack in reverse order.
                PycRef<ASTNode> value = values.back();
                values.pop_back();

                map->add(new ASTObject(key), value);
            }

            print_src(map, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_NAME:
        pyc_output << node.cast<ASTName>()->name()->value();
        break;
    case ASTNode::NODE_NODELIST:
        {
            cur_indent++;
            {
                const auto& nodeList = node.cast<ASTNodeList>()->nodes();
                for (auto ln = nodeList.cbegin(); ln != nodeList.cend();) {
                    // In lambda, detect BLK_IF followed by BLK_ELSE and output as ternary expression
                    if (inLambda && (*ln).cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
                        PycRef<ASTBlock> childBlk = (*ln).cast<ASTBlock>();
                        if (childBlk->blktype() == ASTBlock::BLK_IF) {
                            auto next = ln;
                            ++next;
                            if (next != nodeList.cend() && (*next).cast<ASTNode>().type() == ASTNode::NODE_BLOCK) {
                                PycRef<ASTBlock> nextBlk = (*next).cast<ASTBlock>();
                                if (nextBlk->blktype() == ASTBlock::BLK_ELSE) {
                                    PycRef<ASTCondBlock> ifBlock = childBlk.cast<ASTCondBlock>();
                                    PycRef<ASTCondBlock> elseBlock = nextBlk.cast<ASTCondBlock>();
                                    print_block(ifBlock.cast<ASTBlock>(), mod, pyc_output);
                                    pyc_output << " if ";
                                    print_src(ifBlock->cond(), mod, pyc_output);
                                    pyc_output << " else ";
                                    print_block(elseBlock.cast<ASTBlock>(), mod, pyc_output);
                                    ln++; // skip BLK_IF
                                    ln++; // skip BLK_ELSE
                                    if (ln != nodeList.cend()) {
                                        end_line(pyc_output);
                                    }
                                    continue;
                                }
                            }
                        }
                    }
                    if ((*ln).cast<ASTNode>().type() != ASTNode::NODE_NODELIST) {
                        start_line(cur_indent, pyc_output);
                    }
                    print_src(*ln, mod, pyc_output);
                    end_line(pyc_output);
                    ++ln;
                }
            }
            cur_indent--;
        }
        break;
    case ASTNode::NODE_BLOCK:
        {
            PycRef<ASTBlock> blk = node.cast<ASTBlock>();
            if (blk->blktype() == ASTBlock::BLK_ELSE && blk->size() == 0)
                break;

            if (blk->blktype() == ASTBlock::BLK_CONTAINER) {
                if (blk->size() == 0) {
                    // Empty container - skip to avoid outputting a bare colon
                    break;
                }
                end_line(pyc_output);
                print_block(blk, mod, pyc_output);
                end_line(pyc_output);
                break;
            }

            if (blk->blktype() == ASTBlock::BLK_MAIN) {
                /* BLK_MAIN should only be the root block. If one appears as a
                 * sub-block, it means a FINALLY block from POP_BLOCK was
                 * flattened into the tree without being properly closed.
                 * Skip the block itself and print children inline to avoid
                 * outputting a bare colon (type_str() returns ""). */
                print_block(blk, mod, pyc_output);
                break;
            }

            pyc_output << blk->type_str();
            if (blk->blktype() == ASTBlock::BLK_IF
                    || blk->blktype() == ASTBlock::BLK_ELIF
                    || blk->blktype() == ASTBlock::BLK_WHILE) {
                if (blk.cast<ASTCondBlock>()->negative())
                    pyc_output << " not ";
                else
                    pyc_output << " ";

                print_src(blk.cast<ASTCondBlock>()->cond(), mod, pyc_output);
            } else if (blk->blktype() == ASTBlock::BLK_FOR || blk->blktype() == ASTBlock::BLK_ASYNCFOR) {
                pyc_output << " ";
                PycRef<ASTNode> idx = blk.cast<ASTIterBlock>()->index();
                if (idx == NULL) {
                    // Loop variable couldn't be resolved; use _ as placeholder
                    pyc_output << "_";
                } else if (idx.type() == ASTNode::NODE_OBJECT) {
                    // Index is an object (e.g., Pyc_None) - check if it's actually None
                    PycRef<ASTObject> obj = idx.cast<ASTObject>();
                    if (obj->object().type() == PycObject::TYPE_NONE) {
                        pyc_output << "_";
                    } else {
                        print_src(idx, mod, pyc_output);
                    }
                } else {
                    print_src(idx, mod, pyc_output);
                }
                pyc_output << " in ";
                print_src(blk.cast<ASTIterBlock>()->iter(), mod, pyc_output);
            } else if (blk->blktype() == ASTBlock::BLK_EXCEPT &&
                    blk.cast<ASTCondBlock>()->cond() != NULL) {
                pyc_output << " ";
                print_src(blk.cast<ASTCondBlock>()->cond(), mod, pyc_output);
            } else if (blk->blktype() == ASTBlock::BLK_WITH) {
                pyc_output << " ";
                print_src(blk.cast<ASTWithBlock>()->expr(), mod, pyc_output);
                PycRef<ASTNode> var = blk.try_cast<ASTWithBlock>()->var();
                if (var != NULL) {
                    pyc_output << " as ";
                    print_src(var, mod, pyc_output);
                }
            }
            pyc_output << ":\n";

            cur_indent++;
            print_block(blk, mod, pyc_output);
            cur_indent--;
        }
        break;
        {
            PycRef<PycObject> obj = node.cast<ASTObject>()->object();
            if (obj.type() == PycObject::TYPE_CODE) {
                PycRef<PycCode> code = obj.cast<PycCode>();
                decompyle(code, mod, pyc_output);
            } else {
                print_const(pyc_output, obj, mod);
            }
        }
        break;
    case ASTNode::NODE_PRINT:
        {
            pyc_output << "print ";
            bool first = true;
            if (node.cast<ASTPrint>()->stream() != nullptr) {
                pyc_output << ">>";
                print_src(node.cast<ASTPrint>()->stream(), mod, pyc_output);
                first = false;
            }

            for (const auto& val : node.cast<ASTPrint>()->values()) {
                if (!first)
                    pyc_output << ", ";
                print_src(val, mod, pyc_output);
                first = false;
            }
            if (!node.cast<ASTPrint>()->eol())
                pyc_output << ",";
        }
        break;
    case ASTNode::NODE_RAISE:
        {
            PycRef<ASTRaise> raise = node.cast<ASTRaise>();
            pyc_output << "raise ";
            auto& params = raise->params();
            if (params.size() == 2 && mod->verCompare(3, 0) >= 0) {
                print_src(params.front(), mod, pyc_output);
                pyc_output << " from ";
                print_src(params.back(), mod, pyc_output);
            } else {
                bool first = true;
                for (const auto& param : params) {
                    if (!first)
                        pyc_output << ", ";
                    print_src(param, mod, pyc_output);
                    first = false;
                }
            }
        }
        break;
    case ASTNode::NODE_RETURN:
        {
            PycRef<ASTReturn> ret = node.cast<ASTReturn>();
            PycRef<ASTNode> value = ret->value();
            if (!inLambda) {
                switch (ret->rettype()) {
                case ASTReturn::RETURN:
                    pyc_output << "return ";
                    break;
                case ASTReturn::YIELD:
                    pyc_output << "yield ";
                    break;
                case ASTReturn::YIELD_FROM:
                    if (value.type() == ASTNode::NODE_AWAITABLE) {
                        pyc_output << "await ";
                        value = value.cast<ASTAwaitable>()->expression();
                    } else {
                        pyc_output << "yield from ";
                    }
                    break;
                }
            }
            print_src(value, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_SLICE:
        {
            PycRef<ASTSlice> slice = node.cast<ASTSlice>();

            if (slice->op() & ASTSlice::SLICE1) {
                print_src(slice->left(), mod, pyc_output);
            }
            pyc_output << ":";
            if (slice->op() & ASTSlice::SLICE2) {
                print_src(slice->right(), mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_IMPORT:
        {
            PycRef<ASTImport> import = node.cast<ASTImport>();
            if (import->stores().size()) {
                ASTImport::list_t stores = import->stores();

                pyc_output << "from ";
                if (import->name().type() == ASTNode::NODE_IMPORT)
                    print_src(import->name().cast<ASTImport>()->name(), mod, pyc_output);
                else
                    print_src(import->name(), mod, pyc_output);
                pyc_output << " import ";

                if (stores.size() == 1) {
                    auto src = stores.front()->src();
                    auto dest = stores.front()->dest();
                    print_src(src, mod, pyc_output);

                    if (src.cast<ASTName>()->name()->value() != dest.cast<ASTName>()->name()->value()) {
                        pyc_output << " as ";
                        print_src(dest, mod, pyc_output);
                    }
                } else {
                    bool first = true;
                    for (const auto& st : stores) {
                        if (!first)
                            pyc_output << ", ";
                        print_src(st->src(), mod, pyc_output);
                        first = false;

                        if (st->src().cast<ASTName>()->name()->value() != st->dest().cast<ASTName>()->name()->value()) {
                            pyc_output << " as ";
                            print_src(st->dest(), mod, pyc_output);
                        }
                    }
                }
            } else {
                pyc_output << "import ";
                print_src(import->name(), mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_FUNCTION:
        {
            /* Actual named functions are NODE_STORE with a name */
            pyc_output << "(lambda ";
            PycRef<ASTNode> code = node.cast<ASTFunction>()->code();
            PycRef<PycCode> code_src;
            if (code.type() == ASTNode::NODE_OBJECT) {
                code_src = code.cast<ASTObject>()->object().try_cast<PycCode>();
            }
            if (!code_src) {
                pyc_output << "*_args ";
                cleanBuild = false;
            } else {
                ASTFunction::defarg_t defargs = node.cast<ASTFunction>()->defargs();
                ASTFunction::defarg_t kwdefargs = node.cast<ASTFunction>()->kwdefargs();
                auto da = defargs.cbegin();
                int narg = 0;
                for (int i=0; i<code_src->argCount(); i++) {
                    if (narg)
                        pyc_output << ", ";
                    pyc_output << code_src->getLocal(narg++)->value();
                    if ((code_src->argCount() - i) <= (int)defargs.size()) {
                        pyc_output << " = ";
                        print_src(*da++, mod, pyc_output);
                    }
                }
                da = kwdefargs.cbegin();
                if (code_src->kwOnlyArgCount() != 0) {
                    pyc_output << (narg == 0 ? "*" : ", *");
                    for (int i = 0; i < code_src->argCount(); i++) {
                        pyc_output << ", ";
                        pyc_output << code_src->getLocal(narg++)->value();
                        if ((code_src->kwOnlyArgCount() - i) <= (int)kwdefargs.size()) {
                            pyc_output << " = ";
                            print_src(*da++, mod, pyc_output);
                        }
                    }
                }
            }
            pyc_output << ": ";

            inLambda = true;
            print_src(code, mod, pyc_output);
            inLambda = false;

            pyc_output << ")";
        }
        break;
    case ASTNode::NODE_CLASS:
        {
            PycRef<ASTClass> cls = node.cast<ASTClass>();
            PycRef<ASTNode> cls_name = cls->name();
            PycRef<ASTNode> bases = cls->bases();
            PycRef<ASTNode> code = cls->code();

            pyc_output << "\n";
            start_line(cur_indent, pyc_output);
            pyc_output << "class ";
            if (cls_name.type() == ASTNode::NODE_OBJECT) {
                PycRef<PycObject> name_obj = cls_name.cast<ASTObject>()->object();
                PycRef<PycString> name_str = name_obj.try_cast<PycString>();
                if (name_str) {
                    pyc_output << name_str->value();
                } else {
                    print_src(cls_name, mod, pyc_output);
                }
            } else {
                print_src(cls_name, mod, pyc_output);
            }
            PycRef<ASTTuple> bases_tuple = bases.cast<ASTTuple>();
            if (bases_tuple->values().size() > 0) {
                pyc_output << "(";
                bool first = true;
                for (const auto& val : bases_tuple->values()) {
                    if (!first)
                        pyc_output << ", ";
                    print_src(val, mod, pyc_output);
                    first = false;
                }
                pyc_output << "):\n";
            } else {
                pyc_output << ":\n";
            }
            printClassDocstring = true;
            PycRef<ASTNode> class_body = code.cast<ASTCall>()
                                           ->func().cast<ASTFunction>()->code();
            print_src(class_body, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_STORE:
        {
            PycRef<ASTNode> src = node.cast<ASTStore>()->src();
            PycRef<ASTNode> dest = node.cast<ASTStore>()->dest();
            if (src.type() == ASTNode::NODE_FUNCTION) {
                PycRef<ASTNode> code = src.cast<ASTFunction>()->code();
                PycRef<PycCode> code_src;
                if (code.type() == ASTNode::NODE_OBJECT) {
                    code_src = code.cast<ASTObject>()->object().try_cast<PycCode>();
                }
                if (!code_src) {
                    pyc_output << "\n";
                    start_line(cur_indent, pyc_output);
                    print_src(dest, mod, pyc_output);
                    pyc_output << " = ";
                    print_src(src, mod, pyc_output);
                    cleanBuild = false;
                    break;
                }
                bool isLambda = false;

                if (strcmp(code_src->name()->value(), "<lambda>") == 0) {
                    pyc_output << "\n";
                    start_line(cur_indent, pyc_output);
                    print_src(dest, mod, pyc_output);
                    pyc_output << " = lambda ";
                    isLambda = true;
                } else {
                    pyc_output << "\n";
                    start_line(cur_indent, pyc_output);
                    if (code_src->flags() & PycCode::CO_COROUTINE)
                        pyc_output << "async ";
                    pyc_output << "def ";
                    print_src(dest, mod, pyc_output);
                    pyc_output << "(";
                }

                ASTFunction::defarg_t defargs = src.cast<ASTFunction>()->defargs();
                ASTFunction::defarg_t kwdefargs = src.cast<ASTFunction>()->kwdefargs();
                auto da = defargs.cbegin();
                int narg = 0;
                for (int i = 0; i < code_src->argCount(); ++i) {
                    if (narg)
                        pyc_output << ", ";
                    pyc_output << code_src->getLocal(narg++)->value();
                    if ((code_src->argCount() - i) <= (int)defargs.size()) {
                        pyc_output << " = ";
                        print_src(*da++, mod, pyc_output);
                    }
                }
                da = kwdefargs.cbegin();
                if (code_src->kwOnlyArgCount() != 0) {
                    pyc_output << (narg == 0 ? "*" : ", *");
                    for (int i = 0; i < code_src->kwOnlyArgCount(); ++i) {
                        pyc_output << ", ";
                        pyc_output << code_src->getLocal(narg++)->value();
                        if ((code_src->kwOnlyArgCount() - i) <= (int)kwdefargs.size()) {
                            pyc_output << " = ";
                            print_src(*da++, mod, pyc_output);
                        }
                    }
                }
                if (code_src->flags() & PycCode::CO_VARARGS) {
                    if (narg)
                        pyc_output << ", ";
                    pyc_output << "*" << code_src->getLocal(narg++)->value();
                }
                if (code_src->flags() & PycCode::CO_VARKEYWORDS) {
                    if (narg)
                        pyc_output << ", ";
                    pyc_output << "**" << code_src->getLocal(narg++)->value();
                }

                if (isLambda) {
                    pyc_output << ": ";
                } else {
                    pyc_output << "):\n";
                    printDocstringAndGlobals = true;
                }

                bool preLambda = inLambda;
                inLambda |= isLambda;

                print_src(code, mod, pyc_output);

                inLambda = preLambda;
            } else if (src.type() == ASTNode::NODE_CLASS) {
                pyc_output << "\n";
                start_line(cur_indent, pyc_output);
                pyc_output << "class ";
                print_src(dest, mod, pyc_output);
                PycRef<ASTTuple> bases = src.cast<ASTClass>()->bases().cast<ASTTuple>();
                if (bases->values().size() > 0) {
                    pyc_output << "(";
                    bool first = true;
                    for (const auto& val : bases->values()) {
                        if (!first)
                            pyc_output << ", ";
                        print_src(val, mod, pyc_output);
                        first = false;
                    }
                    pyc_output << "):\n";
                } else {
                    // Don't put parens if there are no base classes
                    pyc_output << ":\n";
                }
                printClassDocstring = true;
                PycRef<ASTNode> code = src.cast<ASTClass>()->code().cast<ASTCall>()
                                       ->func().cast<ASTFunction>()->code();
                print_src(code, mod, pyc_output);
            } else if (src.type() == ASTNode::NODE_IMPORT) {
                PycRef<ASTImport> import = src.cast<ASTImport>();
                if (import->fromlist() != NULL) {
                    PycRef<PycObject> fromlist = import->fromlist().cast<ASTObject>()->object();
                    if (fromlist != Pyc_None) {
                        pyc_output << "from ";
                        if (import->name().type() == ASTNode::NODE_IMPORT)
                            print_src(import->name().cast<ASTImport>()->name(), mod, pyc_output);
                        else
                            print_src(import->name(), mod, pyc_output);
                        pyc_output << " import ";
                        if (fromlist.type() == PycObject::TYPE_TUPLE ||
                                fromlist.type() == PycObject::TYPE_SMALL_TUPLE) {
                            bool first = true;
                            for (const auto& val : fromlist.cast<PycTuple>()->values()) {
                                if (!first)
                                    pyc_output << ", ";
                                pyc_output << val.cast<PycString>()->value();
                                first = false;
                            }
                        } else {
                            pyc_output << fromlist.cast<PycString>()->value();
                        }
                    } else {
                        pyc_output << "import ";
                        print_src(import->name(), mod, pyc_output);
                    }
                } else {
                    pyc_output << "import ";
                    PycRef<ASTNode> import_name = import->name();
                    print_src(import_name, mod, pyc_output);
                    if (!dest.cast<ASTName>()->name()->isEqual(import_name.cast<ASTName>()->name().cast<PycObject>())) {
                        pyc_output << " as ";
                        print_src(dest, mod, pyc_output);
                    }
                }
            } else if (src.type() == ASTNode::NODE_BINARY
                    && src.cast<ASTBinary>()->is_inplace()) {
                print_src(src, mod, pyc_output);
            } else if (src.type() == ASTNode::NODE_CALL
                    && src.cast<ASTCall>()->pparams().size() == 1
                    && src.cast<ASTCall>()->pparams().front().type() == ASTNode::NODE_CLASS) {
                // Decorated class: decorator(class) -> @decorator\nclass X:
                PycRef<ASTCall> outer_call = src.cast<ASTCall>();
                PycRef<ASTNode> decorator = outer_call->func();
                PycRef<ASTNode> cls_node = outer_call->pparams().front();

                // Print decorator(s)
                std::vector<PycRef<ASTNode>> decorators;
                PycRef<ASTNode> cur = decorator;
                while (cur.type() == ASTNode::NODE_CALL) {
                    decorators.push_back(cur);
                    PycRef<ASTCall> cur_call = cur.cast<ASTCall>();
                    if (cur_call->pparams().size() == 1
                        && cur_call->pparams().front().type() == ASTNode::NODE_CLASS) {
                        break;
                    }
                    cur = cur_call->func();
                }

                // Print @decorator lines in reverse (outermost first)
                for (int i = (int)decorators.size() - 1; i >= 0; i--) {
                    PycRef<ASTCall> dec_call = decorators[i].cast<ASTCall>();
                    pyc_output << "\n";
                    start_line(cur_indent, pyc_output);
                    pyc_output << "@";
                    // Print just the function name for the innermost decorator
                    if (i == 0) {
                        print_src(dec_call->func(), mod, pyc_output);
                    } else {
                        print_src(dec_call->func(), mod, pyc_output);
                    }
                    // Print args for this decorator call (excluding the class param at i-1)
                    pyc_output << "(";
                    bool first = true;
                    for (const auto& param : dec_call->pparams()) {
                        if (param.type() == ASTNode::NODE_CLASS && i > 0) continue;
                        if (!first) pyc_output << ", ";
                        print_src(param, mod, pyc_output);
                        first = false;
                    }
                    for (const auto& param : dec_call->kwparams()) {
                        if (!first) pyc_output << ", ";
                        print_src(param.first, mod, pyc_output);
                        pyc_output << " = ";
                        print_src(param.second, mod, pyc_output);
                        first = false;
                    }
                    pyc_output << ")";
                }

                // Print the class itself (without the name since it's in dest)
                PycRef<ASTClass> cls = cls_node.cast<ASTClass>();
                PycRef<ASTNode> bases = cls->bases();
                pyc_output << "\n";
                start_line(cur_indent, pyc_output);
                pyc_output << "class ";
                print_src(dest, mod, pyc_output);
                PycRef<ASTTuple> bases_tuple = bases.try_cast<ASTTuple>();
                if (bases_tuple && bases_tuple->values().size() > 0) {
                    pyc_output << "(";
                    bool first = true;
                    for (const auto& val : bases_tuple->values()) {
                        if (!first) pyc_output << ", ";
                        print_src(val, mod, pyc_output);
                        first = false;
                    }
                    pyc_output << "):\n";
                } else {
                    pyc_output << ":\n";
                }
                printClassDocstring = true;
                PycRef<ASTNode> class_code = cls->code();
                if (class_code.type() == ASTNode::NODE_CALL
                    && class_code.cast<ASTCall>()->func().type() == ASTNode::NODE_FUNCTION) {
                    print_src(class_code.cast<ASTCall>()->func().cast<ASTFunction>()->code(), mod, pyc_output);
                }
            } else {
                print_src(dest, mod, pyc_output);
                pyc_output << " = ";
                print_src(src, mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_CHAINSTORE:
        {
            for (auto& dest : node.cast<ASTChainStore>()->nodes()) {
                print_src(dest, mod, pyc_output);
                pyc_output << " = ";
            }
            print_src(node.cast<ASTChainStore>()->src(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_SUBSCR:
        {
            print_src(node.cast<ASTSubscr>()->name(), mod, pyc_output);
            pyc_output << "[";
            print_src(node.cast<ASTSubscr>()->key(), mod, pyc_output);
            pyc_output << "]";
        }
        break;
    case ASTNode::NODE_AWAITABLE:
        {
            pyc_output << "await ";
            print_src(node.cast<ASTAwaitable>()->expression(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_CONVERT:
        {
            pyc_output << "`";
            print_src(node.cast<ASTConvert>()->name(), mod, pyc_output);
            pyc_output << "`";
        }
        break;
    case ASTNode::NODE_TUPLE:
        {
            PycRef<ASTTuple> tuple = node.cast<ASTTuple>();
            ASTTuple::value_t values = tuple->values();
            if (tuple->requireParens())
                pyc_output << "(";
            bool first = true;
            for (const auto& val : values) {
                if (!first)
                    pyc_output << ", ";
                print_src(val, mod, pyc_output);
                first = false;
            }
            if (values.size() == 1)
                pyc_output << ',';
            if (tuple->requireParens())
                pyc_output << ')';
        }
        break;
    case ASTNode::NODE_ANNOTATED_VAR:
        {
            PycRef<ASTAnnotatedVar> annotated_var = node.cast<ASTAnnotatedVar>();
            PycRef<ASTObject> name = annotated_var->name().cast<ASTObject>();
            PycRef<ASTNode> annotation = annotated_var->annotation();

            pyc_output << name->object().cast<PycString>()->value();
            pyc_output << ": ";
            print_src(annotation, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_TERNARY:
        {
            /* parenthesis might be needed
             * 
             * when if-expr is part of numerical expression, ternary has the LOWEST precedence
             *     print(a + b if False else c)
             * output is c, not a+c (a+b is calculated first)
             * 
             * but, let's not add parenthesis - to keep the source as close to original as possible in most cases
             */
            PycRef<ASTTernary> ternary = node.cast<ASTTernary>();
            //pyc_output << "(";
            print_src(ternary->if_expr(), mod, pyc_output);
            const auto if_block = ternary->if_block().cast<ASTCondBlock>();
            pyc_output << " if ";
            if (if_block->negative())
                pyc_output << "not ";
            print_src(if_block->cond(), mod, pyc_output);
            pyc_output << " else ";
            print_src(ternary->else_expr(), mod, pyc_output);
            //pyc_output << ")";
        }
        break;
    case ASTNode::NODE_UNPACK:
        {
            pyc_output << "*";
            PycRef<ASTNode> val = node.cast<ASTUnpack>()->value();
            // In Python 3.10, {*x if cond else y} is not valid syntax.
            // Force parentheses: {*(x if cond else y)}
            if (val.type() == ASTNode::NODE_TERNARY) {
                pyc_output << "(";
                print_src(val, mod, pyc_output);
                pyc_output << ")";
            } else {
                print_src(val, mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_OBJECT:
        {
            PycRef<ASTObject> obj = node.cast<ASTObject>();
            PycRef<PycObject> pycObj = obj->object();
            if (pycObj.type() == PycObject::TYPE_CODE) {
                /* Code object: decompile and print the actual source */
                PycRef<PycCode> code = pycObj.cast<PycCode>();
                decompyle(code, mod, pyc_output);
            } else {
                /* Other constants: print via print_const */
                print_const(pyc_output, pycObj, mod);
            }
        }
        break;
    default:
        pyc_output << "<NODE:" << node->type() << ">";
        fprintf(stderr, "Unsupported Node type: %d\n", node->type());
        cleanBuild = false;
        node_seen.erase((ASTNode *)node);
        return;
    }

    cleanBuild = true;
    node_seen.erase((ASTNode *)node);
    } catch (const std::bad_cast&) {
        pyc_output << "<bad_cast:node_type=" << node->type() << ">";
        fprintf(stderr, "bad_cast in print_src for node type %d\n", node->type());
        cleanBuild = false;
        node_seen.erase((ASTNode *)node);
    }
}

bool print_docstring(PycRef<PycObject> obj, int indent, PycModule* mod,
                     std::ostream& pyc_output)
{
    // docstrings are translated from the bytecode __doc__ = 'string' to simply '''string'''
    auto doc = obj.try_cast<PycString>();
    if (doc != nullptr) {
        start_line(indent, pyc_output);
        doc->print(pyc_output, mod, true);
        pyc_output << "\n";
        return true;
    }
    return false;
}

static std::unordered_set<PycCode *> code_seen;

void decompyle(PycRef<PycCode> code, PycModule* mod, std::ostream& pyc_output)
{
    if (code_seen.find((PycCode *)code) != code_seen.end()) {
        fputs("WARNING: Circular reference detected\n", stderr);
        return;
    }
    code_seen.insert((PycCode *)code);

    PycRef<ASTNode> source = BuildFromCode(code, mod);

    PycRef<ASTNodeList> clean = source.try_cast<ASTNodeList>();
    if (!clean) {
        clean = new ASTNodeList(ASTNodeList::list_t());
        clean->append(source);
        cleanBuild = false;
    }
    if (cleanBuild) {
        // The Python compiler adds some stuff that we don't really care
        // about, and would add extra code for re-compilation anyway.
        // We strip these lines out here, and then add a "pass" statement
        // if the cleaned up code is empty
        if (clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->src().type() == ASTNode::NODE_NAME
                    && store->dest().type() == ASTNode::NODE_NAME) {
                PycRef<ASTName> src = store->src().cast<ASTName>();
                PycRef<ASTName> dest = store->dest().cast<ASTName>();
                if (src->name()->isEqual("__name__")
                        && dest->name()->isEqual("__module__")) {
                    // __module__ = __name__
                    // Automatically added by Python 2.2.1 and later
                    clean->removeFirst();
                }
            }
        }
        if (clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->src().type() == ASTNode::NODE_OBJECT
                    && store->dest().type() == ASTNode::NODE_NAME) {
                PycRef<ASTObject> src = store->src().cast<ASTObject>();
                PycRef<PycString> srcString = src->object().try_cast<PycString>();
                PycRef<ASTName> dest = store->dest().cast<ASTName>();
                if (dest->name()->isEqual("__qualname__")) {
                    // __qualname__ = '<Class Name>'
                    // Automatically added by Python 3.3 and later
                    clean->removeFirst();
                }
            }
        }

        // Class and module docstrings may only appear at the beginning of their source
        if (printClassDocstring && clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->dest().type() == ASTNode::NODE_NAME &&
                    store->dest().cast<ASTName>()->name()->isEqual("__doc__") &&
                    store->src().type() == ASTNode::NODE_OBJECT) {
                if (print_docstring(store->src().cast<ASTObject>()->object(),
                        cur_indent + (code->name()->isEqual("<module>") ? 0 : 1), mod, pyc_output))
                    clean->removeFirst();
            }
        }
        if (clean->nodes().back().type() == ASTNode::NODE_RETURN) {
            PycRef<ASTReturn> ret = clean->nodes().back().cast<ASTReturn>();

            PycRef<ASTObject> retObj = ret->value().try_cast<ASTObject>();
            if (ret->value() == NULL || ret->value().type() == ASTNode::NODE_LOCALS ||
                    (retObj && retObj->object().type() == PycObject::TYPE_NONE)) {
                clean->removeLast();  // Always an extraneous return statement
            }
        }
    }
    /* Recursively remove trailing return None from block children
       for module-level code. Python adds an implicit return None at
       the end of every code object, but module-level return is not
       valid syntax. The return None can end up inside any block type. */
    if (code->name()->isEqual("<module>")) {
        std::function<void(ASTBlock::list_t&)> cleanBlockReturn;
        cleanBlockReturn = [&](ASTBlock::list_t& nodes) {
            if (nodes.empty()) return;
            for (auto& node : nodes) {
                if (node.type() == ASTNode::NODE_BLOCK) {
                    PycRef<ASTBlock> blk = node.cast<ASTBlock>();
                    auto& children = blk->nodes();
                    if (!children.empty()
                            && children.back().type() == ASTNode::NODE_RETURN) {
                        PycRef<ASTReturn> r = children.back().cast<ASTReturn>();
                        PycRef<ASTObject> rObj = r->value().try_cast<ASTObject>();
                        if (r->value() == NULL
                                || r->value().type() == ASTNode::NODE_LOCALS
                                || (rObj && rObj->object().type() == PycObject::TYPE_NONE)) {
                            children.pop_back();
                        }
                    }
                    cleanBlockReturn(children);
                }
            }
        };
        auto& topNodes = const_cast<ASTNodeList::list_t&>(clean->nodes());
        cleanBlockReturn(topNodes);
    }
    if (printClassDocstring)
        printClassDocstring = false;
    // This is outside the clean check so a source block will always
    // be compilable, even if decompylation failed.
    if (clean->nodes().size() == 0 && !code.isIdent(mod->code())) {
        fprintf(stderr, "[DEBUG] decompyle: '%s' tree empty, adding pass\n", code->name() ? code->name()->value() : "?");
        clean->append(new ASTKeyword(ASTKeyword::KW_PASS));
    }

    bool part1clean = cleanBuild;

    if (printDocstringAndGlobals) {
        if (code->consts()->size())
            print_docstring(code->getConst(0), cur_indent + 1, mod, pyc_output);

        PycCode::globals_t globs = code->getGlobals();
        if (globs.size()) {
            start_line(cur_indent + 1, pyc_output);
            pyc_output << "global ";
            bool first = true;
            for (const auto& glob : globs) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << glob->value();
                first = false;
            }
            pyc_output << "\n";
        }
        printDocstringAndGlobals = false;
    }

    fprintf(stderr, "[DEBUG] decompyle: '%s' tree size=%zu cleanBuild=%d part1clean=%d\n",
            code->name() ? code->name()->value() : "?",
            clean->nodes().size(), cleanBuild, part1clean);

    print_src(source, mod, pyc_output);

    if (!cleanBuild || !part1clean) {
        start_line(cur_indent, pyc_output);
        pyc_output << "# WARNING: Decompyle incomplete\n";
    }

    code_seen.erase((PycCode *)code);
}
