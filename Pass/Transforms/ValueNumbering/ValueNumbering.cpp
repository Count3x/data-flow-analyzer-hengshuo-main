#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/raw_ostream.h"
#include <unordered_map>

using namespace std;
using namespace llvm;

namespace {

    // This method implements what the pass does
    void visitor(Function &F) {
        string func_name = "main";
        errs() << "LivenessAnalysis: " << F.getName() << "\n";

        // Define three pointers to unordered_maps that will be used to store the UEVAR, VARKILL, and LIVEOUT sets for each basic block.
        auto blockUEVar = new unordered_map <string, vector<string>>();
        auto blockVarKill = new unordered_map <string, vector<string>>();
        auto blockLiveOut = new unordered_map <string, vector<string>>();

        for (auto &basic_block: F) {
            // Get the name of the current basic block.
            string blockName = string(basic_block.getName());

            vector <string> VarKill, UEVar;

            for (auto &inst: basic_block) {
                if (inst.getOpcode() == Instruction::Load) {
                    // Get the name of the variable being loaded from memory.
                    string var = string(inst.getOperand(0)->getName());

                    // If the variable being loaded is not already in the VARKILL or UEVAR sets, add it to the UEVAR set.
                    if (count(VarKill.begin(), VarKill.end(), var) == 0 &&
                        count(UEVar.begin(), UEVar.end(), var) == 0) {
                        UEVar.push_back(var);
                    }
                }
                if (inst.getOpcode() == Instruction::Store) {

                    string var1, var2;

                    // If the instruction is a "store" instruction, 
                    // get the names of the variables being stored (if any) from the operands.
                    if (isa<ConstantInt>(inst.getOperand(0))) { // If the first operand is a constant, ignore this 
                        var1 = "";
                    } else {
                        for (int i = 0; i <
                                        2; i++) { // Check whether each operand is a constant integer or a user-defined variable.
                            Value *operand = inst.getOperand(i);
                            if (isa<ConstantInt>(operand)) {
                                if (i == 0) {
                                    var1 = "";
                                } else {
                                    var2 = "";
                                }
                            } else {
                                string operandName = string(dyn_cast<User>(operand)->getOperand(0)->getName());
                                if (i == 0) {
                                    var1 = operandName;
                                } else {
                                    var2 = operandName;
                                }
                            }
                        }

                        if (isa<ConstantInt>(
                                dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))->getOperand(0))->getOperand(0)) ||
                            isa<ConstantInt>(
                                    dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))->getOperand(1))->getOperand(0))) {
                            var1 = "";
                            var2 = "";
                        }
                    }

                    string varName = string(inst.getOperand(1)->getName());

                    // If the variable is not in VarKill and not in UEVar, add it to UEVar.
                    for (string var: {var1, var2}) {
                        if (find(VarKill.begin(), VarKill.end(), var) == VarKill.end() &&
                            find(UEVar.begin(), UEVar.end(), var) == UEVar.end()) {
                            UEVar.emplace_back(var);
                        }
                    }

                    // Add varName to VarKill.
                    if (find(VarKill.begin(), VarKill.end(), varName) == VarKill.end()) {
                        VarKill.emplace_back(varName);
                    }
                }
            }
            // storing the results of the liveness analysis for a basic block
            (*blockUEVar)[blockName] = UEVar;
            (*blockVarKill)[blockName] = VarKill;
        }

        // Initialize the liveOut vector for each basic block to an empty vector.
        for (auto &basic_block: F) {
            (*blockLiveOut)[string(basic_block.getName())] = vector < string > {};
        }


        bool changed;
        do {
            changed = false;
            for (auto &basic_block: F) {
                // Initialize liveOut, unionSuccessor, varKill, and ueVar for the current basic block
                vector <string> liveOut, liveOutTemp, unionSuccessor;

                auto blockLiveOutIt = blockLiveOut->find(string(basic_block.getName()));
                liveOut = blockLiveOutIt->second;

                vector <string> varKill = (*blockVarKill)[string(basic_block.getName())];
                vector <string> ueVar = (*blockUEVar)[string(basic_block.getName())];

                // Compute the union of live variables across all successors
                for (BasicBlock *Succ: successors(&basic_block)) {
                    vector <string> diffTemp, unionTemp;

                    auto blockLiveOutSuccIt = blockLiveOut->find(string(Succ->getName()));
                    vector <string> liveOutSucc = blockLiveOutSuccIt->second;
                    vector <string> varKillSucc = (*blockVarKill)[string(Succ->getName())];
                    vector <string> ueVarSucc = (*blockUEVar)[string(Succ->getName())];

                    set_difference(liveOutSucc.begin(), liveOutSucc.end(), varKillSucc.begin(), varKillSucc.end(),
                                   std::back_inserter(diffTemp));

                    set_union(diffTemp.begin(), diffTemp.end(), ueVarSucc.begin(), ueVarSucc.end(),
                              std::inserter(unionTemp, unionTemp.begin()));
                    unionSuccessor.insert(unionSuccessor.end(), unionTemp.begin(), unionTemp.end());
                }

                // Sort and remove duplicates from the union of live variables across all successors
                std::sort(unionSuccessor.begin(), unionSuccessor.end());
                unionSuccessor.erase(std::unique(unionSuccessor.begin(), unionSuccessor.end()), unionSuccessor.end());

                // Update liveOut if it's different from unionSuccessor.
                if (liveOut != unionSuccessor) {
                    changed = true;
                    blockLiveOutIt->second = unionSuccessor;
                }
            }
        } while (changed);

        // declares a lambda function that sorts the vector and prints out each element separated by spaces
        auto print_vector = [](const vector <string> &vec) {
            for (const auto &elem: vec) {
                errs() << elem << " ";
            }
        };
        // print out-put by format 
        for (auto &basic_block: F) {
            const auto &blockName = string(basic_block.getName());
            vector <string> UEVarTemp = (*blockUEVar)[blockName];
            std::sort(UEVarTemp.begin(), UEVarTemp.end());
            errs() << "----- " << blockName << " -----\n";
            errs() << "UEVAR: ";
            print_vector(UEVarTemp);
            errs() << "\n";

            vector <string> varKillTemp = (*blockVarKill)[blockName];
            std::sort(varKillTemp.begin(), varKillTemp.end());
            errs() << "VARKILL: ";
            print_vector(varKillTemp);
            errs() << "\n";

            vector <string> liveOutTemp = (*blockLiveOut)[blockName];
            std::sort(liveOutTemp.begin(), liveOutTemp.end());
            errs() << "LIVEOUT: ";
            print_vector(liveOutTemp);
            errs() << "\n";
        }

        // prevent memory leaks and free up memory that is no longer needed.
        delete blockUEVar;
        delete blockVarKill;
        delete blockLiveOut;

    }


// New PM implementation
    struct ValueNumberingPass : public PassInfoMixin<ValueNumberingPass> {

        // The first argument of the run() function defines on what level
        // of granularity your pass will run (e.g. Module, Function).
        // The second argument is the corresponding AnalysisManager
        // (e.g ModuleAnalysisManager, FunctionAnalysisManager)
        PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
            visitor(F);
            return PreservedAnalyses::all();


        }

        static bool isRequired() { return true; }
    };
}



//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK

llvmGetPassPluginInfo() {
    return {
            LLVM_PLUGIN_API_VERSION, "ValueNumberingPass", LLVM_VERSION_STRING,
            [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                        [](StringRef Name, FunctionPassManager &FPM,
                           ArrayRef <PassBuilder::PipelineElement>) {
                            if (Name == "value-numbering") {
                                FPM.addPass(ValueNumberingPass());
                                return true;
                            }
                            return false;
                        });
            }};
}
