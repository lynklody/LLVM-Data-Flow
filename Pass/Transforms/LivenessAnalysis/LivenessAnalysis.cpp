#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <list>
#include "llvm/IR/CFG.h"

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "LivenessAnalysis"

namespace {

struct LivenessAnalysis : public FunctionPass {
    string func_name = "test";
    static char ID;
    LivenessAnalysis() : FunctionPass(ID) {}

    //-------------------------KEY VARIABLE DEFINITIONS-----------------------------
    map<Value*, int> vnums;
    map<int, vector<Value*>> vnlist;
    map<int, pair<pair<int, int>, int>> exprvn; 
    int num = 0;
    vector<Value*> allocatedVar;
    map<BasicBlock*, vector<Value*>*> varKillMap;
    map<BasicBlock*, vector<Value*>*> UEVarMap;
    map<BasicBlock*, vector<Value*>*> liveOutMap;
    map<BasicBlock*, vector<Value*>*> liveInMap;
    //-----------------------------------------------------------------------------

    void findVarKill(BasicBlock &bb, vector<Value*> &set) {
        for (auto& inst : bb)
        {
            // Binary opreation: x <- y + z
            if (inst.isBinaryOp()) {
                Value* v = dyn_cast<Value>(&inst);
                int vn = vnums[v];
                vector<Value*> vec = vnlist[vn]; // signiture variable = first element in vnlist Value* vector
                Value* sigvar = vec.at(0);
                if (!findInVec(set, sigvar))
                    set.push_back(sigvar);
            }
            else if (inst.getOpcode() == Instruction::Store) {
                Value* v2;
                if (inst.getNumOperands() == 2)
                    v2 = inst.getOperand(1);
                if (!findInVec(set, v2))
                    set.push_back(v2);
            }
        }
    }

    void findUEVar(BasicBlock &bb, vector<Value*> &set, vector<Value*> &varKill) {
        for (auto& inst : bb)
        {
            if (inst.getOpcode() == Instruction::Alloca 
                || inst.getOpcode() == Instruction::Ret)
                continue;
            Value* ptr = dyn_cast<Value>(&inst);
            Value* v1;
            Value* v2;
            
            if (inst.getNumOperands() >= 1) {
                v1 = inst.getOperand(0);
                if (vnums[v1] && !findInVec(varKill, v1)) {
                    set.push_back(v1);
                }
            }
            if (inst.getNumOperands() == 2) {
                v2 = inst.getOperand(1);
                if (vnums[v2] && !findInVec(varKill, v2)) {
                    set.push_back(v2);
                }
            }
        }
    }

    bool findLiveOut(BasicBlock* bb, vector<Value*>* set) {
        vector<Value*>* live;
        map<BasicBlock*, vector<Value*>*>::iterator it = liveOutMap.find(bb);
        if (it != liveOutMap.end()) {
            live = it->second;
        } else {
            live = new vector<Value*>;
        }
        vector<Value*>* temp;

        for (BasicBlock* succ : successors(bb)) {
            // if (succ) {
                vector<Value*>* liveIn;
                vector<Value*>* varKill;
                vector<Value*>* UEVar;
                vector<Value*>* liveOut;
                map<BasicBlock*, vector<Value*>*>::iterator it;
                
                it = varKillMap.find(succ);
                if (it != varKillMap.end())
                    varKill = it->second;
                it = UEVarMap.find(succ);
                if (it != UEVarMap.end())
                    UEVar = it->second;
                it = liveOutMap.find(succ);
                if (it != liveOutMap.end()) {
                    liveOut = it->second;
                    setDiff(*liveOut, *varKill, *liveIn);
                }
                errs() << "------varkill:\n";
                // printVec(*liveIn);
                vector<Value*> liveIn_after;
                // set_union(liveIn->begin(), liveIn->end(), UEVar->begin(), UEVar->end(),back_inserter(liveIn_after));
                setUnion(*liveIn, *UEVar, liveIn_after);
                errs() << "------liveIn:\n";
                // printVec(*liveIn);
                // set_union(liveIn->begin(), liveIn->end(), UEVar->begin(), UEVar->end(), back_inserter(liveIn));
                setUnion(liveIn_after, *temp, *liveOut);
                errs() << "------liveOut:\n";
                // printVec(*liveOut);
                // set_union(set.begin(), set.end(), temp->begin(), temp->end(), back_inserter(set));
                temp = liveOut;
            // }
        }
        bool changed = false;
        if (liveOutMap.size() != live->size() || it == liveOutMap.end()) {
            changed = true;
        } else {
            vector<Value*>::iterator i;
            for (i = live->begin(); i != live->end(); i++) {
                if (find(temp->begin(), temp->end(), *i) == temp->end()) {
                    changed = true;
                    break;
                }
            }
        }
        if (changed) {
            if (it != liveOutMap.end()) {
                it->second = temp;
            } else {
                liveOutMap.insert(make_pair(bb, temp));
            }
        }
        return changed;
    }

    void valueNumbering(BasicBlock &bb, int &num) {
        for (auto& inst : bb) {

            if (inst.getOpcode() == Instruction::Ret || inst.getOpcode() == Instruction::Br)
                continue;
            // errs() << inst << "\n";

            Value* ptr;
            if (&inst)
                ptr = dyn_cast<Value>(&inst);
            Value* v1;
            Value* v2;
            if (inst.getNumOperands() >= 1) 
                v1 = inst.getOperand(0);
            if (inst.getNumOperands() == 2)
                v2 = inst.getOperand(1);
            stringstream ssptr, ss1, ss2;
            ssptr << ptr;
            ss1 << v1;
            ss2 << v2;
            // errs() << "ptr=" << ptr->getName() << " v1=" << v1->getName() << " v2=" << v2->getName() << "\n";
            // errs() << "ptr=" << ssptr.str() << " v1=" << ss1.str() << " v2=" << ss2.str() << "\n";

            if (inst.getOpcode() == Instruction::Alloca) {
                if (!vnums[ptr]) {
                    vnums[ptr] = ++num;
                    vnlist[num].push_back(ptr);
                    // errs() << num << "\n";
                } else {
                    vnums[ptr] = num + 1;
                    if (!findInVec(vnlist[num], ptr))
                        vnlist[num].push_back(ptr);
                }
                Value* vptr = dyn_cast<Value>(&inst);
                allocatedVar.push_back(vptr);
            }
            else if (inst.getOpcode() == Instruction::Load) {
                // For %0 = load i32, i32* %b, align 4
                // ptr="0" v1="b" v2=""
                // if (!vnums[v1] && !findInVec(vnlist[vnums[v1]], ptr)) {
                if (!vnums[v1]) {
                    errs() << "ERROR! VARIABLE NOT ALLOCATED!\n";
                } else {
                    int prev_vn = vnums[ptr];
                    int vn = vnums[v1];
                    vnums[ptr] = vn;
                    if (prev_vn < vn)
                        vnlist[vn].push_back(ptr);
                    else
                        vnlist[vn].insert(vnlist[vn].begin(), ptr);
                }
            }
            else if (inst.getOpcode() == Instruction::Store) {
                // For store i32 %add, i32* %e, align 4
                // ptr="" v1="add" v2="e"
                if (!vnums[v2]) {
                    int vn = vnums[v1];
                    vnums[v2] == vn;
                    vnlist[vn].push_back(v2);
                } else {
                    int prev_vn = vnums[v2];
                    int vn = vnums[v1];
                    vector<Value*> vec = vnlist[prev_vn];
                    vec.erase(remove(vec.begin(), vec.end(), v2), vec.end());
                    vnums[v2] = vn;
                    if (prev_vn > vn)
                        vnlist[vn].push_back(v2);
                    else
                        vnlist[vn].insert(vnlist[vn].begin(), v2);
                }
            }
            else if (inst.isBinaryOp()) {
                if (!vnums[v1] || !vnums[v2]) {
                    errs() << "ERROR! VARIABLE NOT DECLARED!\n";
                } else {
                    int vn1 = vnums[v1];
                    int vn2 = vnums[v1];
                    // for Instruction::Add, Opcode=13
                    if (!findInExprvn(vn1, vn2, inst.getOpcode())) {
                        exprvn[++num] = make_pair(make_pair(vn1, vn2), inst.getOpcode());
                        vnlist[num].push_back(ptr);
                        vnums[ptr] = num;
                    }
                }
            }
        }
        // printVnums(vnums);
        // printVnlist(vnlist);
    }

    //--------------------------------UTILITY FUNCTIONS-----------------------------
    // find an element in a vector, return the index if found
    bool findInVec(auto &vec, auto target) {
        auto it = find(vec.begin(), vec.end(), target);
        if (it != vec.end()) {
            // return (it-vec.begin());
            return true;
        }
        // return -1;
        return false;
    }

    bool findInExprvn(int vn1, int vn2, int op) {
        for (auto it : exprvn) {
            if (it.second.second == op && it.second.first.first == vn1 && it.second.first.second == vn2)
                return true;
        }
        return false;
    }

    void printVnums(auto &m) {
        for (auto it : m) {
            errs() << it.first->getName() << " " << it.second << "\n";
        }
    }

    void printVnlist(auto &m) {
        for (auto it : m) {
            errs() << "VNLIST[" << it.first << "] ";
            for (auto vec_it : it.second) {
                if(vec_it->getName().empty())
                    errs() << it.first << " ";
                else
                    errs() << vec_it->getName() << " ";
            }
            errs() << "\n";
        }
    }

    bool allocated(Value* v) {
        auto it = find(allocatedVar.begin(), allocatedVar.end(), v);
        if (it != allocatedVar.end()) {
            return true;
        }
        return false;
    }

    void printVec(vector<Value*> vec) {
        // for (vector<Value*>::iterator it: v) {
        for (Value* v: vec) {
            if (allocated(v)) {
                errs() << v->getName() << " ";
            }
        }
        errs() << "\n";
    }

    // void printVec(const vector<Value*>* v) {
    //     // for (Value* v: vec) {
    //     //     if (allocated(v)) {
    //     //         errs() << v->getName() << " ";
    //     //     }
    //     // }
    //     for (auto (*it): (*v)) {
    //         if (allocated((*it))) {
    //             errs() << it->getName() << " ";
    //         }
    //     }
    //     errs() << "\n";
    // }

    void setDiff(vector<Value*> &s1, vector<Value*> &s2, vector<Value*> &s3){
        for (vector<Value*>::iterator it=s1.begin(); it!=s1.end(); it++){
            auto i = find(s2.begin(), s2.end(), (*it));
            if(i == s2.end()){
                s3.insert(s3.end(), (*it));
                errs() <<"\n inserted s3\n";
            }
        }
    }

    // void setDiff(vector<Value*>* s1, vector<Value*>* s2, vector<Value*>* s3){
    //     for (auto it=s1->begin(); it!=s1->end(); it++){
    //         auto i = find(s2->begin(), s2->end(), (*it));
    //         if(i == s2->end()){
    //             // s3->push_back(*it);
    //             s3->insert(s3->end(), (*it));
    //             errs() <<"\n inserted s3\n";
    //         }
    //     }
    // }

    void setUnion(vector<Value*> &s1, vector<Value*> &s2, vector<Value*> &s3){
        errs() << " EMPTY " << s1.empty();
        if (s1.empty() || s2.empty()) {
            return;
        }
        // s3 = s1;
        for (Value* v : s1) {
            s3.push_back(v);
        }
        // for (auto it = s2.begin(); it != s2.end(); it++) {
            // errs() << (*it)->getName() << " ";
        // }
        errs() << "\n";
        // errs() <<"IN SET UNION2\n";
        for (Value* v : s2) {
        // for (vector<Value*>::iterator it = s2.begin(); it != s2.end(); it++){
            // errs() <<"IN SET UNION3\n";
            // errs() << " it=" << v->getName() << "\n";
            // vector<Value*>::iterator i = find(s1.begin(), s1.end(), it);
            if (find(s1.begin(), s1.end(), v) == s1.end()) {
                s3.push_back(v);
                // errs() <<"IN SET UNION4\n";
                // s3->insert(s3->end(), (*it));
            }
        }
    }

    // void setUnion(vector<Value*>* s1, vector<Value*>* s2, vector<Value*>* s3){
    //     s3 = s1;
    //     for (vector<Value*>*::iterator it = s2->begin(); it != s2->end(); it++){
    //         errs() <<"IN SET UNION3\n";
    //         if(find(s1->begin(),s1->end(), (*it)) == s1->end()){
    //             s3->push_back(*it);
    //             errs() <<"IN SET UNION4\n";
    //             // s3->insert(s3->end(), (*it));
    //         }
    //     }
    // }

    //------------------------------------------------------------------------------

    bool runOnFunction(Function &F) override {
        errs() << "Liveness Analysis: " << F.getName() << "\n";
        if (F.getName() != func_name) return false;

        // --------INITIALIZATION-----------
        vector<Value*> varKill;
        vector<Value*> UEVar;
        vector<Value*> liveOut;
        vector<Value*> liveIn;

        // --------ITERATIVE APPROACH--------
        for (auto& basic_block : F) {
            errs() << "----- " << basic_block.getName() << " -----\n";

            valueNumbering(basic_block, num);

            findVarKill(basic_block, varKill);
            varKillMap.insert(make_pair(&basic_block, &varKill));

            findUEVar(basic_block, UEVar, varKill);
            UEVarMap.insert(make_pair(&basic_block, &UEVar));

            errs() << "VARKILL: ";
            printVec(varKill);
            errs() << "UEVAR: ";
            printVec(UEVar);
            
            bool changed =  true;
            while (changed) {
                changed = false;
                changed = findLiveOut(&basic_block, &liveOut);
                errs() << "\nCHANGED=" << changed;
            }
            // liveOutMap.insert(make_pair(&basic_block, &liveOut));

            errs() << "LIVEOUT: ";
            printVec(liveOut);
            varKill.clear();
            UEVar.clear();
            liveOut.clear();
            // // if (liveOut.size() > 0) {
            //     vector<Value*> temp;
            //     // sort(liveOut.begin(), liveOut.end(), comparator());
            //     // sort(varKill.begin(), varKill.end(), comparator());
            //     setDiff(&liveOut, &varKill, &temp);
            //     errs() << "\n--------temp= ";
            //     printVec(temp);
            //     liveOut = temp;
            //     // set_difference(liveOut.begin(), liveOut.end(), varKill.begin(), varKill.end(), back_inserter(liveIn));
            //     // set_difference(liveOut.begin(), liveOut.end(), varKill.begin(), varKill.end(), back_inserter(temp));
            //     // temp.resize(it-temp.begin());
            //     set_union(liveIn.begin(), liveIn.end(), UEVar.begin(), UEVar.end(), back_inserter(liveIn));
            //     liveInMap.insert(make_pair(&basic_block, &liveIn));
            //     // liveInMap.insert(make_pair(&basic_block, &temp));
            //     // printVec(liveIn);
            //     // printVec(temp);
            // // }
            
        // }
        }
    } // end runOnFunction
}; // end of struct
}  // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
