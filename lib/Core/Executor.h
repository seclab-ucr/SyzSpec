//===-- Executor.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Class to perform actual execution, hides implementation details from external
// interpreter.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTOR_H
#define KLEE_EXECUTOR_H

#include "ExecutionState.h"
#include "UserSearcher.h"

#include "klee/ADT/RNG.h"
#include "klee/Core/BranchTypes.h"
#include "klee/Core/Interpreter.h"
#include "klee/Core/TerminationTypes.h"
#include "klee/Expr/ArrayCache.h"
#include "klee/Expr/ArrayExprOptimizer.h"
#include "klee/Module/Cell.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/System/Time.h"

// yuhao: 
#include "klee/Utils/llvm_related.h"
#include "klee/Utils/log.h"
#include "klee/MLTA/Analyzer.h"
#include "klee/MLTA/CallGraph.h"
#include "klee/Specification/Specification.h"
#include "klee/Specification/SpecificationConfig.h"
#include "klee/Specification/SpecificationManager.h"

#include "llvm/ADT/Twine.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <memory>
#include <queue>
#include <set>
#include <string>
#include <sys/types.h>
#include <unordered_map>
#include <vector>

struct KTest;

namespace llvm {
  class BasicBlock;
  class BranchInst;
  class CallInst;
  class LandingPadInst;
  class Constant;
  class ConstantExpr;
  class Function;
  class GlobalValue;
  class Instruction;
  class LLVMContext;
  class DataLayout;
  class Twine;
  class Value;
}

namespace klee {  
  class Array;
  struct Cell;
  class ExecutionState;
  class ExternalDispatcher;
  class Expr;
  class InstructionInfoTable;
  class KCallable;
  struct KFunction;
  struct KInstruction;
  class KInstIterator;
  class KModule;
  class MemoryManager;
  class MemoryObject;
  class ObjectState;
  class PTree;
  class Searcher;
  class SeedInfo;
  class SpecialFunctionHandler;
  struct StackFrame;
  class StatsTracker;
  class TimingSolver;
  class TreeStreamWriter;
  class MergeHandler;
  class MergingSearcher;
  template<class T> class ref;



  /// \todo Add a context object to keep track of data only live
  /// during an instruction step. Should contain addedStates,
  /// removedStates, and haltExecution, among others.

class Executor : public Interpreter {
  friend class OwningSearcher;
  friend class WeightedRandomSearcher;
  friend class SpecialFunctionHandler;
  friend class StatsTracker;
  friend class MergeHandler;
  friend klee::Searcher *klee::constructUserSearcher(Executor &executor);

public:
  typedef std::pair<ExecutionState*,ExecutionState*> StatePair;

  /// The random number generator.
  RNG theRNG;

private:
  std::unique_ptr<KModule> kmodule;
  InterpreterHandler *interpreterHandler;
  Searcher *searcher;

  ExternalDispatcher *externalDispatcher;
  std::unique_ptr<TimingSolver> solver;
  std::unique_ptr<MemoryManager> memory;
  std::set<ExecutionState*, ExecutionStateIDCompare> states;
  StatsTracker *statsTracker;
  TreeStreamWriter *pathWriter, *symPathWriter;
  SpecialFunctionHandler *specialFunctionHandler;
  TimerGroup timers;
  std::unique_ptr<PTree> processTree;

  /// Used to track states that have been added during the current
  /// instructions step. 
  /// \invariant \ref addedStates is a subset of \ref states. 
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> addedStates;
  /// Used to track states that have been removed during the current
  /// instructions step. 
  /// \invariant \ref removedStates is a subset of \ref states. 
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::vector<ExecutionState *> removedStates;

  /// When non-empty the Executor is running in "seed" mode. The
  /// states in this map will be executed in an arbitrary order
  /// (outside the normal search interface) until they terminate. When
  /// the states reach a symbolic branch then either direction that
  /// satisfies one or more seeds will be added to this map. What
  /// happens with other states (that don't satisfy the seeds) depends
  /// on as-yet-to-be-determined flags.
  std::map<ExecutionState*, std::vector<SeedInfo> > seedMap;

  /// Map of globals to their representative memory object.
  std::map<const llvm::GlobalValue*, MemoryObject*> globalObjects;

  /// Map of globals to their bound address. This also includes
  /// globals that have no representative object (e.g. aliases).
  std::map<const llvm::GlobalValue*, ref<ConstantExpr>> globalAddresses;

  /// Map of legal function addresses to the corresponding Function.
  /// Used to validate and dereference function pointers.
  std::unordered_map<std::uint64_t, llvm::Function*> legalFunctions;

  // yuhao: find function address 
  std::unordered_map<llvm::Function*, std::uint64_t> legalFunctionsAddress;

  /// When non-null the bindings that will be used for calls to
  /// klee_make_symbolic in order replay.
  const struct KTest *replayKTest;

  /// When non-null a list of branch decisions to be used for replay.
  const std::vector<bool> *replayPath;

  /// The index into the current \ref replayKTest or \ref replayPath
  /// object.
  unsigned replayPosition;

  /// When non-null a list of "seed" inputs which will be used to
  /// drive execution.
  const std::vector<struct KTest *> *usingSeeds;  

  /// Disables forking, instead a random path is chosen. Enabled as
  /// needed to control memory usage. \see fork()
  bool atMemoryLimit;

  /// Disables forking, set by client. \see setInhibitForking()
  bool inhibitForking;

  /// Signals the executor to halt execution at the next instruction
  /// step.
  bool haltExecution;  

  /// Whether implied-value concretization is enabled. Currently
  /// false, it is buggy (it needs to validate its writes).
  bool ivcEnabled;

  /// The maximum time to allow for a single core solver query.
  /// (e.g. for a single STP query)
  time::Span coreSolverTimeout;

  /// Maximum time to allow for a single instruction.
  time::Span maxInstructionTime;

  /// Assumes ownership of the created array objects
  ArrayCache arrayCache;

  /// File to print executed instructions to
  std::unique_ptr<llvm::raw_ostream> debugInstFile;

  // @brief Buffer used by logBuffer
  std::string debugBufferString;

  // @brief buffer to store logs before flushing to file
  llvm::raw_string_ostream debugLogBuffer;

  /// Optimizes expressions
  ExprOptimizer optimizer;

  /// Points to the merging searcher of the searcher chain,
  /// `nullptr` if merging is disabled
  MergingSearcher *mergingSearcher = nullptr;

  /// Typeids used during exception handling
  std::vector<ref<Expr>> eh_typeids;

  /// Return the typeid corresponding to a certain `type_info`
  ref<ConstantExpr> getEhTypeidFor(ref<Expr> type_info);

  llvm::Function* getTargetFunction(llvm::Value *calledVal);
  
  void executeInstruction(ExecutionState &state, KInstruction *ki);

  void run(ExecutionState &initialState);

  // Given a concrete object in our [klee's] address space, add it to 
  // objects checked code can reference.
  MemoryObject *addExternalObject(ExecutionState &state, void *addr, 
                                  unsigned size, bool isReadOnly);

  void initializeGlobalAlias(const llvm::Constant *c);
  void initializeGlobalObject(ExecutionState &state, ObjectState *os, const llvm::Value *v,
			      const llvm::Constant *c,
			      unsigned offset,
            // yuhao: 
            bool symbolic = false);
  
  // yuhao: 
  void initializeGlobalObject(ExecutionState &state, ObjectState *os, const llvm::Value *v,
            llvm::Type *t,
            unsigned offset,
            bool only_pointer = false);

  void initializeGlobals(ExecutionState &state);
  void allocateGlobalObjects(ExecutionState &state);
  void initializeGlobalAliases();
  void initializeGlobalObjects(ExecutionState &state);

  void stepInstruction(ExecutionState &state);
  void updateStates(ExecutionState *current);
  void transferToBasicBlock(llvm::BasicBlock *dst, 
			    llvm::BasicBlock *src,
			    ExecutionState &state);

  void callExternalFunction(ExecutionState &state,
                            KInstruction *target,
                            KCallable *callable,
                            std::vector< ref<Expr> > &arguments);

  ObjectState *bindObjectInState(ExecutionState &state, const MemoryObject *mo,
                                 bool isLocal, const Array *array = 0);

  /// Resolve a pointer to the memory objects it could point to the
  /// start of, forking execution when necessary and generating errors
  /// for pointers to invalid locations (either out of bounds or
  /// address inside the middle of objects).
  ///
  /// \param results[out] A list of ((MemoryObject,ObjectState),
  /// state) pairs for each object the given address can point to the
  /// beginning of.
  typedef std::vector< std::pair<std::pair<const MemoryObject*, const ObjectState*>, 
                                 ExecutionState*> > ExactResolutionList;
  void resolveExact(ExecutionState &state,
                    ref<Expr> p,
                    ExactResolutionList &results,
                    const std::string &name);

  /// Allocate and bind a new object in a particular state. NOTE: This
  /// function may fork.
  ///
  /// \param isLocal Flag to indicate if the object should be
  /// automatically deallocated on function return (this also makes it
  /// illegal to free directly).
  ///
  /// \param target Value at which to bind the base address of the new
  /// object.
  ///
  /// \param reallocFrom If non-zero and the allocation succeeds,
  /// initialize the new object from the given one and unbind it when
  /// done (realloc semantics). The initialized bytes will be the
  /// minimum of the size of the old and new objects, with remaining
  /// bytes initialized as specified by zeroMemory.
  ///
  /// \param allocationAlignment If non-zero, the given alignment is
  /// used. Otherwise, the alignment is deduced via
  /// Executor::getAllocationAlignment
  // yuhao: set zeroMemory to true for the Linux kernel
  void executeAlloc(ExecutionState &state,
                    ref<Expr> size,
                    bool isLocal,
                    KInstruction *target,
                    bool zeroMemory=true,
                    const ObjectState *reallocFrom=0,
                    size_t allocationAlignment=0);

  /// Free the given address with checking for errors. If target is
  /// given it will be bound to 0 in the resulting states (this is a
  /// convenience for realloc). Note that this function can cause the
  /// state to fork and that \ref state cannot be safely accessed
  /// afterwards.
  void executeFree(ExecutionState &state,
                   ref<Expr> address,
                   KInstruction *target = 0);

  /// Serialize a landingpad instruction so it can be handled by the
  /// libcxxabi-runtime
  MemoryObject *serializeLandingpad(ExecutionState &state,
                                    const llvm::LandingPadInst &lpi,
                                    bool &stateTerminated);

  /// Unwind the given state until it hits a landingpad. This is used
  /// for exception handling.
  void unwindToNextLandingpad(ExecutionState &state);

  void executeCall(ExecutionState &state, 
                   KInstruction *ki,
                   llvm::Function *f,
                   std::vector< ref<Expr> > &arguments);
                   
  // do address resolution / object binding / out of bounds checking
  // and perform the operation
  void executeMemoryOperation(ExecutionState &state,
                              bool isWrite,
                              ref<Expr> address,
                              ref<Expr> value /* undef if read */,
                              KInstruction *target /* undef if write */,
                              int64_t operand = 0 /* operand of address */,
                              uint64_t _size = 0 /* size of value */);

  void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo,
                           const std::string &name);

  /// Create a new state where each input condition has been added as
  /// a constraint and return the results. The input state is included
  /// as one of the results. Note that the output vector may include
  /// NULL pointers for states which were unable to be created.
  void branch(ExecutionState &state, const std::vector<ref<Expr>> &conditions,
              std::vector<ExecutionState *> &result, BranchType reason);

  /// Fork current and return states in which condition holds / does
  /// not hold, respectively. One of the states is necessarily the
  /// current state, and one of the states may be null.
  StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal,
                 BranchType reason);

  // If the MaxStatic*Pct limits have been reached, concretize the condition and
  // return it. Otherwise, return the unmodified condition.
  ref<Expr> maxStaticPctChecks(ExecutionState &current, ref<Expr> condition);

  /// Add the given (boolean) condition as a constraint on state. This
  /// function is a wrapper around the state's addConstraint function
  /// which also manages propagation of implied values,
  /// validity checks, and seed patching.
  void addConstraint(ExecutionState &state, ref<Expr> condition);

  // Called on [for now] concrete reads, replaces constant with a symbolic
  // Used for testing.
  ref<Expr> replaceReadWithSymbolic(ExecutionState &state, ref<Expr> e);

  const Cell& eval(KInstruction *ki, unsigned index, 
                   ExecutionState &state) const;

  Cell& getArgumentCell(ExecutionState &state,
                        KFunction *kf,
                        unsigned index) {
    return state.stack.back().locals[kf->getArgRegister(index)];
  }

  Cell& getDestCell(ExecutionState &state,
                    KInstruction *target) {
    return state.stack.back().locals[target->dest];
  }

  void bindLocal(KInstruction *target, 
                 ExecutionState &state, 
                 ref<Expr> value);
  void bindArgument(KFunction *kf, 
                    unsigned index,
                    ExecutionState &state,
                    ref<Expr> value);

  /// Evaluates an LLVM constant expression.  The optional argument ki
  /// is the instruction where this constant was encountered, or NULL
  /// if not applicable/unavailable.
  ref<klee::ConstantExpr> evalConstantExpr(const llvm::ConstantExpr *c,
					   const KInstruction *ki = NULL);

  /// Evaluates an LLVM constant.  The optional argument ki is the
  /// instruction where this constant was encountered, or NULL if
  /// not applicable/unavailable.
  ref<klee::ConstantExpr> evalConstant(const llvm::Constant *c,
				       const KInstruction *ki = NULL);

  /// Return a unique constant value for the given expression in the
  /// given state, if it has one (i.e. it provably only has a single
  /// value). Otherwise return the original expression.
  ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &e);

  /// Return a constant value for the given expression, forcing it to
  /// be constant in the given state by adding a constraint if
  /// necessary. Note that this function breaks completeness and
  /// should generally be avoided.
  ///
  /// \param purpose An identify string to printed in case of concretization.
  ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e, 
                                     const char *purpose);

  /// Bind a constant value for e to the given target. NOTE: This
  /// function may fork state if the state has multiple seeds.
  void executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target);

  /// Get textual information regarding a memory address.
  std::string getAddressInfo(ExecutionState &state, ref<Expr> address) const;

  // Determines the \param lastInstruction of the \param state which is not KLEE
  // internal and returns its InstructionInfo
  const InstructionInfo & getLastNonKleeInternalInstruction(const ExecutionState &state,
      llvm::Instruction** lastInstruction);

  /// Remove state from queue and delete state. This function should only be
  /// used in the termination functions below.
  void terminateState(ExecutionState &state);

  /// Call exit handler and terminate state normally
  /// (end of execution path)
  void terminateStateOnExit(ExecutionState &state);

  /// Call exit handler and terminate state early
  /// (e.g. due to state merging or memory pressure)
  void terminateStateEarly(ExecutionState &state, const llvm::Twine &message,
                           StateTerminationType reason);

  /// Call exit handler and terminate state early
  /// (e.g. caused by the applied algorithm as in state merging or replaying)
  void terminateStateEarlyAlgorithm(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason);

  /// Call exit handler and terminate state early
  /// (e.g. due to klee_silent_exit issued by user)
  void terminateStateEarlyUser(ExecutionState &state,
                               const llvm::Twine &message);

  /// Call error handler and terminate state in case of errors.
  /// The underlying function of all error-handling termination functions
  /// below. This function should only be used in the termination functions
  /// below.
  void terminateStateOnError(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason,
                                    const llvm::Twine &longMessage = "",
                                    const char *suffix = nullptr);

  /// Call error handler and terminate state in case of program errors
  /// (e.g. free()ing globals, out-of-bound accesses)
  void terminateStateOnProgramError(ExecutionState &state,
                                    const llvm::Twine &message,
                                    StateTerminationType reason,
                                    const llvm::Twine &longMessage = "",
                                    const char *suffix = nullptr);

  /// Call error handler and terminate state in case of execution errors
  /// (things that should not be possible, like illegal instruction or
  /// unlowered intrinsic, or unsupported intrinsics, like inline assembly)
  void terminateStateOnExecError(
      ExecutionState &state, const llvm::Twine &message,
      StateTerminationType = StateTerminationType::Execution);

  /// Call error handler and terminate state in case of solver errors
  /// (solver error or timeout)
  void terminateStateOnSolverError(ExecutionState &state,
                                   const llvm::Twine &message);

  /// Call error handler and terminate state for user errors
  /// (e.g. wrong usage of klee.h API)
  void terminateStateOnUserError(ExecutionState &state,
                                 const llvm::Twine &message);

  /// bindModuleConstants - Initialize the module constant table.
  void bindModuleConstants();

  template <typename TypeIt>
  void computeOffsetsSeqTy(KGEPInstruction *kgepi,
                           ref<ConstantExpr> &constantOffset, uint64_t index,
                           const TypeIt it);

  template <typename TypeIt>
  void computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie);

  /// bindInstructionConstants - Initialize any necessary per instruction
  /// constant values.
  void bindInstructionConstants(KInstruction *KI);

  void doImpliedValueConcretization(ExecutionState &state,
                                    ref<Expr> e,
                                    ref<ConstantExpr> value);

  /// check memory usage and terminate states when over threshold of -max-memory + 100MB
  /// \return true if below threshold, false otherwise (states were terminated)
  bool checkMemoryUsage();

  /// check if branching/forking is allowed
  bool branchingPermitted(const ExecutionState &state) const;

  void printDebugInstructions(ExecutionState &state);
  void doDumpStates();

  /// Only for debug purposes; enable via debugger or klee-control
  void dumpStates();
  void dumpPTree();

public:
  Executor(llvm::LLVMContext &ctx, const InterpreterOptions &opts,
      InterpreterHandler *ie);
  virtual ~Executor();

  const InterpreterHandler& getHandler() {
    return *interpreterHandler;
  }

  void setPathWriter(TreeStreamWriter *tsw) override { pathWriter = tsw; }

  void setSymbolicPathWriter(TreeStreamWriter *tsw) override {
    symPathWriter = tsw;
  }

  void setReplayKTest(const struct KTest *out) override {
    assert(!replayPath && "cannot replay both buffer and path");
    replayKTest = out;
    replayPosition = 0;
  }

  void setReplayPath(const std::vector<bool> *path) override {
    assert(!replayKTest && "cannot replay both buffer and path");
    replayPath = path;
    replayPosition = 0;
  }

  llvm::Module *setModule(std::vector<std::unique_ptr<llvm::Module>> &modules,
                          const ModuleOptions &opts) override;

  void useSeeds(const std::vector<struct KTest *> *seeds) override {
    usingSeeds = seeds;
  }
  // yuhao:
  void prepare_for_kernel();
  void runFunctionAsMain(llvm::Function *f, int argc, char **argv,
                         char **envp) override;
  void runEntryFunction(ExecutionState *state, llvm::Function *f, int argc, char **argv,
                         char **envp);

  /*** Runtime options ***/

  void setHaltExecution(bool value) override { haltExecution = value; }

  void setInhibitForking(bool value) override { inhibitForking = value; }

  void prepareForEarlyExit() override;

  /*** State accessor methods ***/

  unsigned getPathStreamID(const ExecutionState &state) override;

  unsigned getSymbolicPathStreamID(const ExecutionState &state) override;

  void getConstraintLog(const ExecutionState &state, std::string &res,
                        Interpreter::LogType logFormat =
                            Interpreter::STP) override;

  bool getSymbolicSolution(
      const ExecutionState &state,
      std::vector<std::pair<std::string, std::vector<unsigned char>>> &res)
      override;

  void getCoveredLines(const ExecutionState &state,
                       std::map<const std::string *, std::set<unsigned>> &res)
      override;

  Expr::Width getWidthForLLVMType(llvm::Type *type) const;
  size_t getAllocationAlignment(const llvm::Value *allocSite) const;

  /// Returns the errno location in memory of the state
  int *getErrnoLocation(const ExecutionState &state) const;

  MergingSearcher *getMergingSearcher() const { return mergingSearcher; };
  void setMergingSearcher(MergingSearcher *ms) { mergingSearcher = ms; };

  // yuhao: type based call graph
  std::unordered_map<llvm::FunctionType *, std::set<llvm::Function *> *> map_function_type;
  GlobalContext GlobalCtx;
  void multi_layer_type_analysis(); 

  // yuhao: for multiple entry functions
  std::queue<llvm::Function *> entry_functions;

  // yuhao: add new entry functions from kernel
  void update_entry_functions();

  // yuhao: states before running
  std::vector<ExecutionState *> states_before_running;
  // yuhao: states after running
  std::vector<ExecutionState *> states_after_running;

  // yuhao: kernel specific
  hy::SpecificationConfig spec_config;

  // yuhao: symbolic variables
  std::string get_symbolic_name(std::string name, uint64_t &count,
                                std::string prefix = "") {
    std::string ret;
    ret += name + DELIMITER + std::to_string(count++);
    if (prefix != "") {
      ret += DELIMITER + prefix;
    }
    return ret;
  }

  std::string global_name = "global";
  uint64_t global_count = 0;
  std::string current_global_name;
  std::string get_global_name() {
    return get_symbolic_name(global_name, global_count, current_global_name);
  }

  std::string input_name = "input";
  uint64_t input_count = 0;

  std::string asm_return_name = "asm_return";
  uint64_t asm_return_count = 0;

  std::string external_return_name = "external_return";
  uint64_t external_return_count = 0;

  std::string special_function_name = "special_function";
  uint64_t special_function_count = 0;

  std::string alloc_name = "alloc";
  uint64_t alloc_count = 0;

  std::string uc_name = "under_constrained";
  uint64_t uc_count = 0;
  std::string get_uc_name(std::string prefix = "") {
    char delimiter = DELIMITER;
    std::vector<std::string> substrings;
    size_t startPos = 0;
    size_t endPos = prefix.find(delimiter);

    while (endPos != std::string::npos) {
      std::string substring = prefix.substr(startPos, endPos - startPos);
      substrings.push_back(substring);

      startPos = endPos + 1;
      endPos = prefix.find(delimiter, startPos);
    }

    if (startPos < prefix.length()) {
      std::string substring = prefix.substr(startPos);
      substrings.push_back(substring);
    }

    prefix = "";
    for (auto substring : substrings) {
      if (substring == input_name) {
        prefix = substring;
        break;
      } else if (substring == global_name) {
        break;
      }
    }

    return get_symbolic_name(uc_name, uc_count, prefix);
  }

  bool print = false;

  // yuhao: create a symbolic value
  ref<Expr> manual_make_symbolic(ExecutionState &state, 
                                 const std::string &symbolic_name,
                                 const llvm::Value *allocSite, 
                                 uint64_t type_store_size,
                                 uint64_t type_load_size,
                                 llvm::Type *ty = nullptr);

  // yuhao: create symbolic arguments
  std::vector<ref<Expr>> user_arguments;
  std::vector<llvm::Type *> user_arguments_type;

  hy::SpecificationManager spec_manager;

  ref<Expr> create_symbolic_arg(ExecutionState &state,
                                const llvm::Value *allocSite, llvm::Type *ty,
                                bool is_input = true);

  // yuhao: for expr arg
  uint64_t specification_handle(ExecutionState &state);

  // yuhao: for each type
  hy::Type *specification_handle_type(ExecutionState &state, llvm::Type *ty,
                                      ref<Expr> expr = nullptr,
                                      const ObjectState *os = nullptr,
                                      uint64_t offset = 0);

  // yuhao: for each ucmo
  uint64_t specification_handle_ucmo(ExecutionState &state,
                                     under_constrained_memory_object *ucmo,
                                     hy::PointerType *pty);

  hy::Type *specification_handle_pointer(ExecutionState &state, llvm::Type *ty, ref<Expr> expr);

  // yuhao: check whether the ucmo has possible types
  uint64_t get_ucmo_type(under_constrained_memory_object *ucmo);

  // yuhao:
  hy::Direction check_direction(const ObjectState *os);

  // yuhao:
  void add_mo_type(ExecutionState &state, const MemoryObject *mo, llvm::Type *_type);

  // yuhao: specification guided fork
  class fork_point {
  public:
    uint64_t total = 0;
    uint64_t total_true = 0;
    uint64_t total_false = 0;
    uint64_t total_new_specifications = 0;
    uint64_t total_new_specifications_true = 0;
    uint64_t total_new_specifications_false = 0;
    void add(bool branch, uint64_t new_specification, uint64_t count = 1) {
      total += count;
      if (branch) {
        total_true += count;
      } else {
        total_false += count;
      }
      if (new_specification > 0) {
        total_new_specifications += count;
        if (branch) {
          total_new_specifications_true += count;
        } else {
          total_new_specifications_false += count;
        }
      }
    }
  };

  std::map<llvm::Instruction *, fork_point *> fork_points;

  void update_fork_points(ExecutionState &state, uint64_t ret);

  void specification_guided_fork(Executor::StatePair &branches, llvm::Instruction *inst);

  // yuhao: create a mo with one whole symbolic value, return the mo
  MemoryObject *create_ucmo(ExecutionState &state, const std::string &name,
                            const llvm::Value *allocSite,
                            uint64_t type_store_size, llvm::Type *ty = nullptr);

  // yuhao: operate on symbolic expressions
  std::string get_name(ref<Expr> value);

  void resolve_symbolic_expr(ref<Expr> expr, std::set<std::string> &names, uint64_t count = 0);

  void resolve_symbolic_expr(ref<Expr> expr, std::set<ref<Expr>> &vars);

  bool is_related(std::set<std::string> names, const std::string &name);

  bool is_all_related(std::set<std::string> names, const std::string &name);

  // yuhao: check whether there are related constraints
  bool is_related_ucmo_constraints(ExecutionState &state, std::set<ref<Expr>> vars);

  // yuhao: forward and backward type trace
  // forward mainly for nested structures
  bool backward_trace(llvm::Value *value, llvm::Type **type, bool &has_offset,
                      llvm::Instruction **base_inst);

  // yuhao: currently, we do not perform forward trace
  bool forward_trace(llvm::Value *value, llvm::Type **type, bool &has_offset,
                     ref<Expr> &base);

  // yuhao: read the value of arguments for inst
  Cell &un_eval(KInstruction *ki, unsigned index, ExecutionState &state) const;

  // yuhao: read the value from address, not work for under constrained memory
  ref<Expr> read_value_from_address(ExecutionState &state,
                                    const ref<Expr> &address, Expr::Width type);

  // yuhao: others
  llvm::Module *get_module();

  bool special_function(llvm::Function *f);

  bool get_memory_object(ObjectPair &op, ExecutionState &state,
                       ref<Expr> address);

  bool get_memory_object(ObjectPair &op, ExecutionState &state,
                       under_constrained_memory_object *ucmo);

  // yuhao: similar to toUnique but with smo constraint
  ref<Expr> toUnique_ucmo(const ExecutionState &state, ref<Expr> &e);

  // yuhao: similar to toUnique but with cond
  ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &new_cond, ref<Expr> &e);

  // yuhao: similar to toConstant but with smo constraint
  ref<klee::ConstantExpr> get_constant_smo(ExecutionState &state, ref<Expr> e,
                                         const char *purpose);

  // yuhao: get range with smo constraints
  std::pair<ref<Expr>, ref<Expr>> to_range_smo(const ExecutionState &state,
                                               ref<Expr> &e);

  // yuhao: is a meaningful range or not
  // if the range is [0, -1], it is not meaningful
  bool is_meaningful_range(ref<Expr> &low, ref<Expr> &high);

  // yuhao: get value of expr
  // constant, range, 
  void get_value(ExecutionState &state, ref<Expr> expr, hy::Value *value);

  // check whether a integer expr is a pointer. 
  // integer could be a pointer, for the integer has the same width as the pointer. 
  // if we can find the ucmo, no matter whether we create memory object for it. 
  // we think it is a pointer 
  // do not consider the case that the int has the same value as the pointer
  bool is_pointer(ExecutionState &state, llvm::Type *ty, ref<Expr> expr,
                  under_constrained_memory_object **ucmo);

  // yuhao: find under constrained memory object with the same base address
  // if not find, create a new one
  // always try to find the smo is created
  under_constrained_memory_object *create_ucmo_by_base_address(ExecutionState &state,
                                                 ref<Expr> base_address);

  // yuhao: find under constrained memory object with the same base address
  under_constrained_memory_object *
  find_ucmo_by_base_address(ExecutionState &state, ref<Expr> base_address);

  // yuhao: find under constrained memory object including the address
// 1. smo with the same base address and created mo
// 2. smo within the range and created mo
// 3. smo with the closest base address and created mo: for resize and relocate
  under_constrained_memory_object *find_ucmo_flexible(ExecutionState &state,
                                            ref<Expr> base_address,
                                            ref<Expr> address);

  // yuhao: "operand" means the operand number of the address in the target instruction
  // store the possible type of the address in the "type"
  ref<Expr> find_base_address(ExecutionState &state, ref<Expr> address,
                              KInstruction *target = nullptr,
                              int64_t operand = 0, llvm::Type **type = nullptr);

  // yuhao: for linked list
  void record_linked_list(ExecutionState &state, KInstruction *ki);
  void maintain_linked_list(ExecutionState &state, KInstruction *ki,
                            bool is_write, MemoryObject *mo, ref<Expr> address);

  // yuhao: analysis for the copy_from_user, copy_to_user, memdup_user
  void type_analysis(ExecutionState &state, KInstruction *ki, Function *f,
                     std::vector<ref<Expr>> &arguments);

  // yuhao: get the number of symbolic pointer and possible target mo
  void statistic_symbolic_poineter(ExecutionState &state, ref<Expr> address, unsigned bytes);
};
  
} // End klee namespace

#endif /* KLEE_EXECUTOR_H */
