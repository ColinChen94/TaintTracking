//
// Created by yuxuan chen on 2/21/19.
//

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instruction.h"
#include <map>
#include <vector>
#include <iostream>
using namespace llvm;

namespace {
    // vector to store the direction of the branch.
    typedef std::vector<uint8_t> Dir, *DirPtr;

    // Basic blick information.
    class BBInfo {
    public:
        Value* label;
        // For branches, it's OK to use bit to represent which direction, but for switch, we have to use > 2 number to represent each branch.
        DirPtr branches;
        Instruction* ancestor; // last branch in the main path.
        BBInfo* parent;

        BBInfo(Value* label, DirPtr ptr, Instruction* ancestor, BBInfo* parent): label(label), branches(ptr), ancestor(ancestor), parent(parent) {};
        ~BBInfo() {
            delete branches;
        }
    };

    // For easy use of current basic block information
    BBInfo* curBBInfo_ptr;

    // Rust lib function address.
    Constant *tree_new, *table_new, *bitvec_new, *insert_c, *union_c, *bitvec_set, *bitvec_print, *tree_free, *table_free, *bitvec_free;
    StructType *tree_type, *table_type, *bitvec_type;
    PointerType *tree_ptr, *table_ptr, *bitvec_ptr;
    Type *int32_type, *void_type;
    GlobalVariable *root, *nodes;
    Value *root_ptr, *nodes_ptr;
    Constant* zero;

    std::map<Function*, GlobalVariable*> FcnToBBLabelMap;
    std::map<Function*, std::vector<GlobalVariable*>*> FcnToArgsTaintsMap;
    std::map<Function*, GlobalVariable*> FcnToRtnTaintMap;

    // Must use a whole map for tmp and mem since there might be some global variables shared by different functions.
    std::map<Value*, Value*> TmpToLabelMap;

    // Must allocate a space to store the label since different branches might access the same mem,
    // which have different impacts on the label.
    // So it is impossible for a map to store two label for the same mem in that case.
    // There is no such problem for register (tmp) since each instruction has its own number.
    std::map<Value*, Value*> MemToLabelAddrMap;

    // A mapping from BasicBlock pointer to Basic block information.
    // Since the pointer address might be operated in different branches.
    std::map<BasicBlock*, BBInfo*> BBToBBInfoMap;

    // To track branch taint.
    // The variable can be mutable only via phinode or store.
    // If the branch use store, the address should go to this map and be tainted to the lable of that block.
    // So when we load that mem block, the taint will be pass to the load value.
    std::map<Value*, std::vector<BBInfo*>*> AddrToBBInfosMap;
    uint64_t NumOfTaints;

    struct TaintTrackingPass : public ModulePass {
        static char ID;
        TaintTrackingPass() : ModulePass(ID) {}

        struct TaintTrackingVisitor: InstVisitor<TaintTrackingVisitor> {

            TaintTrackingVisitor() {}

            // Store will change the state of the program.
            void visitStoreInst(StoreInst &I) {
                auto reg_iter1 = TmpToLabelMap.find(I.getValueOperand());
                auto reg_iter2 = TmpToLabelMap.find(I.getPointerOperand());

                insertAddrTaint(I.getPointerOperand());

                Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;

                if (reg_iter1 == TmpToLabelMap.end() && reg_iter2 == TmpToLabelMap.end()) {
                    auto mem_iter = MemToLabelAddrMap.find(I.getPointerOperand());
                    if (mem_iter == MemToLabelAddrMap.end()) {
                        MemToLabelAddrMap[I.getPointerOperand()] = alocaAndStoreLabel(curBBInfo_ptr->label,
                                                                                      insert_point);
                    }
                    return;
                }

                Value* label = curBBInfo_ptr->label;
                if (reg_iter1 != TmpToLabelMap.end() && reg_iter2 != TmpToLabelMap.end()) {
                    label = union_taint(label, reg_iter1->second, &I);
                    label = union_taint(label, reg_iter2->second, &I);
                } else if (reg_iter1 != TmpToLabelMap.end()) {
                    label = union_taint(label, reg_iter1->second, &I);
                } else {
                    label = union_taint(label, reg_iter2->second, &I);
                }

                auto mem_iter = MemToLabelAddrMap.find(I.getPointerOperand());
                if (mem_iter != MemToLabelAddrMap.end()) {
                    storeLabel(label, mem_iter->second, &I);
                } else {
                    MemToLabelAddrMap[I.getPointerOperand()] = alocaAndStoreLabel(label, &I);
                }
            }

            void insertAddrTaint(Value* addr) {
                auto bbinfos_iter = AddrToBBInfosMap.find(addr);

                if (curBBInfo_ptr->branches->size() == 0) {
                    // in main path
                    if (bbinfos_iter == AddrToBBInfosMap.end()) {
                        return;
                    } else {
                        bbinfos_iter->second->clear();
                        return;
                    }
                } else {
                    // No record.
                    if (bbinfos_iter == AddrToBBInfosMap.end()) {
                        std::vector<BBInfo *> *bbinfos_vec = new std::vector<BBInfo *>;
                        bbinfos_vec->push_back(curBBInfo_ptr);
                        AddrToBBInfosMap[addr] = bbinfos_vec;
                    } else if (bbinfos_iter->second->size() == 0) {
                        bbinfos_iter->second->push_back(curBBInfo_ptr);
                    } else {
                        BBInfo *lastbbinfo_ptr = bbinfos_iter->second->back();
                        if (lastbbinfo_ptr->ancestor == curBBInfo_ptr->ancestor) {

                            if (lastbbinfo_ptr->branches->size() < curBBInfo_ptr->branches->size()) {
                                if (isEmbeded(curBBInfo_ptr->branches, lastbbinfo_ptr->branches)) {
                                    bbinfos_iter->second->pop_back();
                                }
                                bbinfos_iter->second->push_back(curBBInfo_ptr);
                            } else if (lastbbinfo_ptr->branches->size() > curBBInfo_ptr->branches->size()) {
                                if (isEmbeded(lastbbinfo_ptr->branches, curBBInfo_ptr->branches)) {
                                    bbinfos_iter->second->pop_back();
                                }
                                bbinfos_iter->second->push_back(curBBInfo_ptr);
                            } else {
                                uint8_t lasttemp = lastbbinfo_ptr->branches->back();
                                uint8_t curtemp = curBBInfo_ptr->branches->back();
                                lastbbinfo_ptr->branches->pop_back();
                                curBBInfo_ptr->branches->pop_back();

                                if (!isEmbeded(lastbbinfo_ptr->branches, curBBInfo_ptr->branches)) {
                                    bbinfos_iter->second->push_back(curBBInfo_ptr);
                                }

                                lastbbinfo_ptr->branches->push_back(lasttemp);
                                curBBInfo_ptr->branches->push_back(curtemp);
                            }
                        } else { // Different ancestor
                            bbinfos_iter->second->push_back(curBBInfo_ptr);
                        }
                    }
                }
            }

            bool isEmbeded(DirPtr LongVec, DirPtr ShortVec) {
                unsigned int num = ShortVec->size();
                for (unsigned int index = 0; index < num; index++) {
                    if (LongVec->at(index) != ShortVec->at(index)) {
                        return false;
                    }
                }
                return true;
            }

            // x = a[i] means the register is tainted by the pointer a and index i.
            // And we also need to check if the address is tainted in loop.
            void visitLoadInst(LoadInst &I) {
                auto addr_iter = MemToLabelAddrMap.find(I.getPointerOperand());
                auto reg_iter = TmpToLabelMap.find(I.getPointerOperand());
                auto bbinfos_iter = AddrToBBInfosMap.find(I.getPointerOperand());
                Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;

                if (addr_iter == MemToLabelAddrMap.end() && reg_iter == TmpToLabelMap.end()) {
                    if (bbinfos_iter == AddrToBBInfosMap.end()) {
                        return;
                    }
                    std::vector<BBInfo*>* bbinfos_ptr = bbinfos_iter->second;
                    if (bbinfos_ptr->size() == 0) {
                        return;
                    } else if (bbinfos_ptr->size() == 1){
                        TmpToLabelMap[&I] = bbinfos_ptr->back()->label;
                        return;
                    } else {
                        Value* label = bbinfos_ptr->front()->label;
                        auto vec_iter = bbinfos_ptr->begin();
                        vec_iter++;
                        for ( ; vec_iter != bbinfos_ptr->end(); vec_iter++) {
                            label = union_taint(label, (*vec_iter)->label, insert_point);
                        }
                        TmpToLabelMap[&I] = label;
                        return;
                    }
                }

                Value* label;
                if (addr_iter != MemToLabelAddrMap.end() && reg_iter != TmpToLabelMap.end()) {
                    label = loadLabel(addr_iter->second, insert_point);
                    label = union_taint(label, reg_iter->second, insert_point);
                } else if (addr_iter != MemToLabelAddrMap.end()) {
                    label = loadLabel(addr_iter->second, insert_point);
                } else {
                    label = reg_iter->second;
                }

                if (bbinfos_iter == AddrToBBInfosMap.end()) {
                    TmpToLabelMap[&I] = label;
                    return;
                }

                std::vector<BBInfo*>* bbinfos_ptr = bbinfos_iter->second;
                if (bbinfos_ptr->size() == 0) {
                    TmpToLabelMap[&I] = label;
                    return;
                } else if (bbinfos_ptr->size() == 1){
                    TmpToLabelMap[&I] = union_taint(label, bbinfos_ptr->front()->label, insert_point);
                    return;
                } else {
                    for ( auto vec_iter = bbinfos_ptr->begin(); vec_iter != bbinfos_ptr->end(); vec_iter++) {
                        label = union_taint(label, (*vec_iter)->label, insert_point);
                    }
                    TmpToLabelMap[&I] = label;
                    return;
                }
            }

            // TODO: pass taint label of callee basic block
            // since the block might embeded in conditional statement
            // and the procedure touch memory, which means that mem block is tainted by the condition.
            void visitCallInst(CallInst &I) {
                Function* called = I.getCalledFunction();
                unsigned int total = I.getNumArgOperands();

                // For defined function, we have the chance to track the taint of return value.
                if (called->hasExactDefinition()) {
                    storeLabel(curBBInfo_ptr->label, FcnToBBLabelMap.find(called)->second, &I);

                    std::vector<GlobalVariable*>* argsTaint = FcnToArgsTaintsMap[called];
                    for (unsigned int index = 0; index < total; index++) {
                        auto reg_iter = TmpToLabelMap.find(I.getArgOperand(index));
                        if (reg_iter != TmpToLabelMap.end()) {
                            storeLabel(reg_iter->second, argsTaint->at(index), &I);
                        } else {
                            storeLabel(zero, argsTaint->at(index), &I);
                        }
                    }

                    if (called->getReturnType() != void_type) {
                        IRBuilder<> builder(&I);
                        builder.SetInsertPoint(I.getParent(), ++builder.GetInsertPoint());
                        GlobalVariable *RtnTaint = FcnToRtnTaintMap[called];
                        Value *label = builder.CreateLoad(int32_type, RtnTaint);
                        TmpToLabelMap[&I] = label;
                    }

                } else if (called->getName() == "__isoc99_scanf") {
                    Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;

                    // TODO: consider the scanf is in branch
                    // a[i] = x means the memory block is both tainted by the i and x.
                    for (unsigned int index = 1; index < total; index++) {
                        Value *label = insert_taint(insert_point);
                        Value *addr = I.getArgOperand(index);
                        auto reg_iter = TmpToLabelMap.find(addr);
                        if (reg_iter != TmpToLabelMap.end()) {
                            label = union_taint(label, reg_iter->second, insert_point);
                        }
                        auto mem_iter = MemToLabelAddrMap.find(addr);
                        if (mem_iter != MemToLabelAddrMap.end()) {
                            storeLabel(label, mem_iter->second, insert_point);
                        } else {
                            MemToLabelAddrMap[addr] = alocaAndStoreLabel(label, insert_point);
                        }

                        insertAddrTaint(addr);
                    }

                } else {
                    // For extern function, just assume the returned value is Or'ed by all of the function arguments.
                    Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;
                    if (called->getReturnType() != void_type) {

                        bool hasTaint = false;
                        Value *temp;

                        for (unsigned int index = 0; index < total; index++) {
                            auto reg_iter = TmpToLabelMap.find(I.getArgOperand(index));
                            if (reg_iter != TmpToLabelMap.end()) {
                                if (hasTaint) {
                                    temp = union_taint(temp, reg_iter->second, insert_point);
                                } else {
                                    temp = reg_iter->second;
                                    hasTaint = true;
                                }
                            }
                        }

                        if (hasTaint) {
                            TmpToLabelMap[&I] = temp;
                        }
                    }
                }
            }

            void visitReturnInst(ReturnInst &I) {
                Function *callee = I.getFunction();
                // TODO: print out taints of all the blocks
                if (callee->getName() == "main") {
//                    Constant* totalNum = ConstantInt::get(int32_type, NumOfTaints);
//                    for (auto bbinfo_iter = BBToBBInfoMap.begin(); bbinfo_iter != BBToBBInfoMap.end(); bbinfo_iter++) {
//                        IRBuilder<> builder(&I);
//                        Value* bitvec_print_args[] = {nodes_ptr, bbinfo_iter->second->label, totalNum};
//                        builder.CreateCall(bitvec_print, bitvec_print_args);
//                    }
                } else {
                    // TODO: need to union the old label and new label and store the label.
                    if (callee->getReturnType() != void_type) {
                        IRBuilder<> builder(&I);
                        GlobalVariable *RtnTaint = FcnToRtnTaintMap[callee];

                        auto reg_iter = TmpToLabelMap.find(I.getReturnValue());
                        if (reg_iter != TmpToLabelMap.end()) {
                            builder.CreateStore(reg_iter->second, RtnTaint);
                        } else {
                            builder.CreateStore(ConstantInt::get(int32_type, 0), RtnTaint);
                        }
                    }
                }
            }

            // TODO: Allocate memory to store the taint instead of using map
            // Since there is a tiny possiblity that the address might be tainted by different input.
            // a + i = a + j
            // But commom things faster and first
            void visitGetElementPtrInst(GetElementPtrInst &I) {
                bool hasTaint = false;
                Value *temp;

                auto reg_iter = TmpToLabelMap.find(I.getPointerOperand());
                if (reg_iter != TmpToLabelMap.end()) {
                    temp = reg_iter->second;
                    hasTaint = true;
                }

                Instruction* insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;
                for (auto index = I.idx_begin(); index != I.idx_end(); index++) {
                    reg_iter = TmpToLabelMap.find((Value*) *index);
                    if (reg_iter != TmpToLabelMap.end()) {
                        if (hasTaint) {
                            temp = union_taint(temp, reg_iter->second, insert_point);
                        } else {
                            temp = reg_iter->second;
                            hasTaint = true;
                        }
                    }
                }

                if (hasTaint) {
                    TmpToLabelMap[&I] = temp;
                }

            }

            // The BranchAnalysis is not very accurate so far
            // TODO: add commands to analyze loop.
            void visitBranchInst(BranchInst &I) {
                if (I.isUnconditional()) {
                    BasicBlock *successor = I.getSuccessor(0);
                    auto iter = BBToBBInfoMap.find(successor);

                    // If not in the map, the taint is equal to the taint of n-1 level.
                    // TODO: double check if it's a loop.
                    // Since loop also has a unconditional branch jumping to it.
                    if (iter == BBToBBInfoMap.end()) {
                        if (NumLoops(successor) == 0) {
                            DirPtr Dirtemp = new Dir(*curBBInfo_ptr->branches);
                            Dirtemp->pop_back();
                            BBInfo* BBtemp;
                            BBtemp = new BBInfo(curBBInfo_ptr->parent->label, Dirtemp, (Dirtemp->size() == 0)? successor->getTerminator(): curBBInfo_ptr->ancestor,
                                                                  (Dirtemp->size() == 0)? BBtemp: curBBInfo_ptr->parent->parent);
                            BBToBBInfoMap[successor] = BBtemp;
                        }
                    }
                } else {
                    // An assumption from obsevation: successor1 comes after successor2
                    BasicBlock *successor0 = I.getSuccessor(0);
                    BasicBlock *successor1 = I.getSuccessor(1);

                    // No need since terminator is branch.
                    // Instruction* insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;

                    auto reg_iter = TmpToLabelMap.find(I.getCondition());
                    Value *label;
                    if (reg_iter != TmpToLabelMap.end()) {
                        label = union_taint(curBBInfo_ptr->label, reg_iter->second, curBBInfo_ptr->ancestor);
                    } else {
                        label = curBBInfo_ptr->label;
                    }
                    // One from current branch, the other from successor1
                    // TODO: double check if there is a loop.
                    DirPtr Dirtemp0 = new Dir(*curBBInfo_ptr->branches);
                    DirPtr Dirtemp1 = new Dir(*curBBInfo_ptr->branches);

                    if (successor1->getNumUses() - NumLoops(successor1) >= 2) {
                        auto iter1 = BBToBBInfoMap.find(successor1);

                        if (iter1 == BBToBBInfoMap.end()) {
                            BBInfo* BBtemp1;
                            BBtemp1 = new BBInfo(curBBInfo_ptr->label, Dirtemp1, (Dirtemp1->size() == 0)? successor1->getTerminator(): curBBInfo_ptr->ancestor,
                                    (Dirtemp1->size() == 0)? BBtemp1: curBBInfo_ptr->parent);
                            BBToBBInfoMap[successor1] = BBtemp1;
                        }
                    } else {
                        // Deeper level
                        Dirtemp1->push_back(1);
                        BBInfo* BBtemp1 = new BBInfo(label, Dirtemp1, curBBInfo_ptr->ancestor, curBBInfo_ptr);
                        BBToBBInfoMap[successor1] = BBtemp1;
                    }

                    Dirtemp0->push_back(0);
                    BBInfo* BBtemp0 = new BBInfo(label, Dirtemp0, curBBInfo_ptr->ancestor, curBBInfo_ptr);
                    BBToBBInfoMap[successor0] = BBtemp0;
                }
            }

            void visitBinaryOperator(BinaryOperator &I) {
                visitBinOp(I);
            }

            // There might be some weird predicate like x < x
            // have to enumerate them in the future.
            void visitICmpInst(ICmpInst &I) {
                visitBinOp(I);
            }

            void visitBinOp(Instruction &I) {
                Value *operand1 = I.getOperand(0);
                Value *operand2 = I.getOperand(1);

                auto reg_iter1 = TmpToLabelMap.find(operand1);
                auto reg_iter2 = TmpToLabelMap.find(operand2);

                Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;
                if (reg_iter1 != TmpToLabelMap.end() && reg_iter2 != TmpToLabelMap.end()) {
                    TmpToLabelMap[&I] = union_taint(reg_iter1->second, reg_iter2->second, insert_point);
                } else if (reg_iter1 != TmpToLabelMap.end()) {
                    TmpToLabelMap[&I] = reg_iter1->second;
                } else if (reg_iter2 != TmpToLabelMap.end()) {
                    TmpToLabelMap[&I] = reg_iter2->second;
                }
            }

            // TODO: Add another phinode to do dynamic analysis.
            // Since the destination is tainted by all the blocks and one value.
            void visitPHINode(PHINode &I) {
                Value *label = zero;

                Instruction *insert_point = (curBBInfo_ptr->branches->size() == 0)? &I: curBBInfo_ptr->ancestor;
                unsigned int num = I.getNumIncomingValues();
                for (unsigned int index = 0; index < num; index++) {
                    auto reg_iter = TmpToLabelMap.find(I.getIncomingValue(index));
                    auto bb_iter = BBToBBInfoMap.find(I.getIncomingBlock(index));
                    if (reg_iter != TmpToLabelMap.end()) {
                        label = union_taint(label, bb_iter->second->label, insert_point);
                    } else {
                        label = union_taint(label, bb_iter->second->label, insert_point);
                        label = union_taint(label, reg_iter->second, insert_point);
                    }
                }

                TmpToLabelMap[&I] = label;
            }

            Value* alocaAndStoreLabel(Value *label, Instruction *I) {
                IRBuilder<> builder(I);
                Instruction *addr = builder.CreateAlloca(int32_type);
                builder.CreateStore(label, addr);
                return addr;
            }

            void storeLabel(Value *label, Value *addr, Instruction *I) {
                IRBuilder<> builder(I);
                builder.CreateStore(label, addr);
                return;
            }

            Value* loadLabel(Value *addr, Instruction *I) {
                IRBuilder<> builder(I);
                return builder.CreateLoad(int32_type, addr);
            }

            Value* insert_taint(Instruction *I) {
                IRBuilder<> builder(I);
                Value* bitvec = builder.CreateCall(bitvec_new);
                Value* bitvec_set_args[] = {bitvec, ConstantInt::get(int32_type, 1), ConstantInt::get(int32_type, NumOfTaints++)};
                builder.CreateCall(bitvec_set, bitvec_set_args);
                Value* insert_c_args[] = {root_ptr, bitvec, nodes_ptr};
                Value* label = builder.CreateCall(insert_c, insert_c_args);
                Value* bitvec_free_args[] = {bitvec};
                builder.CreateCall(bitvec_free, bitvec_free_args);
                return label;
            }

            Value* union_taint(Value *label1, Value *label2, Instruction *I) {
                IRBuilder<> builder(I);
                Value* args[] = { label1, label2, nodes_ptr, root_ptr };
                return builder.CreateCall(union_c, args);
            }

            // TODO:
            bool NoLoop(BasicBlock* bb) {
                return true;
            }

            // TODO:
            unsigned NumLoops(BasicBlock* successor) {
                return 0;
            }
        };

        TaintTrackingVisitor TaintVisitor;

        // Declare all the extern function from rust tool lib
        // Get some necessary stucture and pointer types
        void FuncDeclare(Module &M) {
            LLVMContext &Ctx = M.getContext();

            // Get necessary types
            int32_type = Type::getInt32Ty(Ctx);
            void_type = Type::getVoidTy(Ctx);
            bitvec_type = StructType::create(Ctx, "bitvec");
            bitvec_ptr = bitvec_type->getPointerTo();
            tree_type = StructType::create(Ctx, "tree");
            tree_ptr = tree_type->getPointerTo();
            table_type = StructType::create(Ctx, "table");
            table_ptr = table_type->getPointerTo();

            // For extern function bitvec_new()
            std::vector<Type*> bitvec_new_params;
            FunctionType *bitvec_new_fn = FunctionType::get(bitvec_ptr, bitvec_new_params, false);
            bitvec_new = M.getOrInsertFunction("bitvec_new", bitvec_new_fn);

            // For extern function bitvec_set()
            std::vector<Type*> bitvec_set_params = { bitvec_ptr, int32_type, int32_type };
            FunctionType *bitvec_set_fn = FunctionType::get(void_type, bitvec_set_params, false);
            bitvec_set = M.getOrInsertFunction("bitvec_set", bitvec_set_fn);

            // For extern function bitvec_print()
            std::vector<Type*> bitvec_print_params = { table_ptr, int32_type, int32_type, int32_type };
            FunctionType *bitvec_print_fn = FunctionType::get(void_type, bitvec_print_params, false);
            bitvec_print = M.getOrInsertFunction("bitvec_print", bitvec_print_fn);

            // For extern function bitvec_free()
            std::vector<Type*> bitvec_free_params = { bitvec_ptr };
            FunctionType *bitvec_free_fn = FunctionType::get(void_type, bitvec_free_params, false);
            bitvec_free = M.getOrInsertFunction("bitvec_free", bitvec_free_fn);

            // For extern function tree_new()
            std::vector<Type*> tree_new_params;
            FunctionType *tree_new_fn = FunctionType::get(tree_ptr, tree_new_params, false);
            tree_new = M.getOrInsertFunction("tree_new", tree_new_fn);

            // For extern function tree_free()
            std::vector<Type*> tree_free_params = { tree_ptr };
            FunctionType *tree_free_fn = FunctionType::get(void_type, tree_free_params, false);
            tree_free = M.getOrInsertFunction("tree_free", tree_free_fn);

            // For extern function table_new()
            std::vector<Type*> table_new_params;
            FunctionType *table_new_fn = FunctionType::get(table_ptr, table_new_params, false);
            table_new = M.getOrInsertFunction("table_new", table_new_fn);

            // For extern function table_free()
            std::vector<Type*> table_free_params = { table_ptr };
            FunctionType *table_free_fn = FunctionType::get(void_type, table_free_params, false);
            table_free = M.getOrInsertFunction("table_free", table_free_fn);

            // For extern function insert_c()
            std::vector<Type*> insert_c_params = { tree_ptr, bitvec_ptr, table_ptr };
            FunctionType *insert_c_fn = FunctionType::get(int32_type, insert_c_params, false);
            insert_c = M.getOrInsertFunction("insert_c", insert_c_fn);

            // For extern function union_c()
            std::vector<Type*> union_c_params = { int32_type, int32_type, table_ptr, tree_ptr };
            FunctionType *union_c_fn = FunctionType::get(int32_type, union_c_params, false);
            union_c = M.getOrInsertFunction("union_c", union_c_fn);

        }

        void AllocGlobalVal(Module &M) {
            root = new GlobalVariable(M, tree_ptr, false, GlobalValue::ExternalLinkage, 0, "root");
            nodes = new GlobalVariable(M, table_ptr, false, GlobalValue::ExternalLinkage, 0, "nodes");
            root->setInitializer(ConstantPointerNull::get(tree_ptr));
            nodes->setInitializer(ConstantPointerNull::get(table_ptr));
        }

        void AllocDefineFcnArgsTaints(Module &M) {
            for (auto &F: M) {
                if (F.hasExactDefinition()) {
                    if (F.getName() == "main") {
                        continue;
                    } else {
                        std::vector<GlobalVariable*> *currentTaints = new std::vector<GlobalVariable*>();
                        for(auto arg = F.arg_begin(); arg != F.arg_end(); arg++) {
                            GlobalVariable* temp = new GlobalVariable(M, int32_type, false, GlobalValue::ExternalLinkage, 0);
                            temp->setInitializer(zero);
                            currentTaints->push_back(temp);
                        }
                        FcnToArgsTaintsMap[&F] = currentTaints;
                    }
                }
            }
        }

        void AllocDefineFcnRtnTaint(Module &M) {
            for (auto &F: M) {
                if (F.hasExactDefinition()) {
                    if (F.getName() == "main") {
                        continue;
                    } else {
                        GlobalVariable *temp = new GlobalVariable(M, int32_type, false, GlobalValue::ExternalLinkage, 0);
                        temp->setInitializer(zero);
                        FcnToRtnTaintMap[&F] = temp;
                    }
                }
            }
        }

        void AllocDefineFcnBBLabel(Module &M) {
            for (auto &F: M) {
                if (F.hasExactDefinition()) {
                    if (F.getName() == "main") {
                        continue;
                    } else {
                        GlobalVariable *temp = new GlobalVariable(M, int32_type, false, GlobalValue::ExternalLinkage, 0);
                        FcnToBBLabelMap[&F] = temp;
                    }
                }
            }
        }

        void InitializeMainArgs(Function &F) {
            NumOfTaints = 0;

            BasicBlock &BB = F.getEntryBlock();
            IRBuilder<> builder(&BB, BB.getFirstInsertionPt());
            root_ptr = builder.CreateCall(tree_new);
            nodes_ptr = builder.CreateCall(table_new);
            builder.CreateStore(root_ptr, root);
            builder.CreateStore(nodes_ptr, nodes);

            // Entry block is always untainted.
            zero = ConstantInt::get(int32_type, 0);
            Value* bitvec = builder.CreateCall(bitvec_new);
            Value* bitvec_set_args[] = {bitvec, zero, zero};
            builder.CreateCall(bitvec_set, bitvec_set_args);
            Value* insert_c_args[] = {root_ptr, bitvec, nodes_ptr };
            Value* label = builder.CreateCall(insert_c, insert_c_args);
            Value* bitvec_free_args[] = {bitvec};
            builder.CreateCall(bitvec_free, bitvec_free_args);

            DirPtr Dirtemp = new Dir;
            BBInfo *BBtemp;
            BBtemp = new BBInfo(label, Dirtemp, BB.getTerminator(), BBtemp);
            BBToBBInfoMap[&BB] = BBtemp;

            for (auto arg = F.arg_begin(); arg != F.arg_end(); arg++) {
                Value* bitvec = builder.CreateCall(bitvec_new);
                // Type is the basic unit.
                Value* bitvec_set_args[] = {bitvec, ConstantInt::get(int32_type, 1), ConstantInt::get(int32_type, NumOfTaints++)};
                builder.CreateCall(bitvec_set, bitvec_set_args);
                Value* insert_c_args[] = {root_ptr, bitvec, nodes_ptr };
                Value* label = builder.CreateCall(insert_c, insert_c_args);
                Value* bitvec_free_args[] = {bitvec};
                builder.CreateCall(bitvec_free, bitvec_free_args);
                TmpToLabelMap[arg] = label;
            }

        }

        void InitializeDefineFcnArgsAndLabel(Function &F) {
            BasicBlock & BB = F.getEntryBlock();

            IRBuilder<> builder(&BB, BB.getFirstInsertionPt());

            // We have to reload the label in case the function is called under a branch.
            Value* BBlabel = builder.CreateLoad(int32_type, FcnToBBLabelMap[&F]);

            DirPtr Dirtemp = new Dir;
            BBInfo *BBtemp;
            BBtemp = new BBInfo(BBlabel, Dirtemp, BB.getTerminator(), BBtemp);
            BBToBBInfoMap[&BB] = BBtemp;

            root_ptr = builder.CreateLoad(tree_ptr, root);
            nodes_ptr = builder.CreateLoad(table_ptr, nodes);

            std::vector<GlobalVariable*>* argsTaint = FcnToArgsTaintsMap[&F];
            unsigned int index = 0;
            for (auto arg = F.arg_begin(); arg != F.arg_end(); arg++, index++) {
                Value* label = builder.CreateLoad(int32_type, argsTaint->at(index));
                TmpToLabelMap[arg] = label;
            }
        }

        virtual bool runOnModule(Module &M) {
            // Get the function to call from our runtime library.
            FuncDeclare(M);
            AllocGlobalVal(M);
            AllocDefineFcnArgsTaints(M);
            AllocDefineFcnRtnTaint(M);
            AllocDefineFcnBBLabel(M);

            for (auto &F: M) {
                if (F.hasExactDefinition()) {
                    std::vector<std::vector<Instruction*>*> FcnInstrList;
                    std::vector<BasicBlock*> FcnBBList;

                    for (auto &B: F) {
                        std::vector<Instruction*>* temp = new std::vector<Instruction*>;
                        FcnBBList.push_back(&B);
                        for (auto &I: B) {
                            temp->push_back(&I);
                        }
                        FcnInstrList.push_back(temp);
                    }

                    if (F.getName() == "main") {
                        InitializeMainArgs(F);
                    } else {
                        InitializeDefineFcnArgsAndLabel(F);
                    }
                    auto bb_iter = FcnBBList.begin();
                    for (auto bbinstr_iter = FcnInstrList.begin(); bbinstr_iter != FcnInstrList.end() && bb_iter
                            != FcnBBList.end(); bbinstr_iter++, bb_iter++) {
                        curBBInfo_ptr = BBToBBInfoMap.find(*bb_iter)->second;
                        std::vector<Instruction*>* bbinstrs = *bbinstr_iter;
                        for (auto instr_iter = bbinstrs->begin(); instr_iter != bbinstrs->end(); instr_iter++) {
                            //(*instr_iter)->print(errs());
                            //std::cout << std::endl;
                            TaintVisitor.visit(**instr_iter);
                        }
                    }

                    display(FcnBBList);
                    //std::cout << "-----------------------" << std::endl;
                }
            }

            //print(M);

            return true;

        }

        void print(Module &M) {
            std::cout << std::endl;
            for (auto &F: M) {
                errs() << F.getName() << " "<< F.hasExactDefinition() << "\n";
                if (F.hasExactDefinition()) {
                    for (auto &B: F)
                        for (auto &I: B) {
                            I.print(errs());
                            errs() << I.getName();
                            errs() << "\n";
                        }
                }
            }
        }

        void display(std::vector<BasicBlock*> &B) {
            unsigned int total = B.size();
            Constant* totalNum = ConstantInt::get(int32_type, NumOfTaints);
            for (unsigned int id = 0; id < total; id++) {
                auto bbinfo_iter = BBToBBInfoMap.find(B.at(id));
                IRBuilder<> builder(B[total-1]->getTerminator());
                Value* bitvec_print_args[] = {nodes_ptr, bbinfo_iter->second->label, totalNum, ConstantInt::get(int32_type, id)};
                builder.CreateCall(bitvec_print, bitvec_print_args);
            }
        }

    };
}

char TaintTrackingPass::ID = 0;

//Automatically enable the pass.
//http://adriansampson.net/blog/clangpass.html
static void registerTaintTrackingPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM) {
    PM.add(new TaintTrackingPass());
}

static RegisterStandardPasses
        RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly, registerTaintTrackingPass);

static RegisterStandardPasses
        RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerTaintTrackingPass);
