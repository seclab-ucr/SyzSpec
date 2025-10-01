//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Executor.h"

#include "AddressSpace.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExecutionState.h"
#include "ExternalDispatcher.h"
#include "GetElementPtrTypeIterator.h"
#include "ImpliedValue.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"

#include "klee/ADT/KTest.h"
#include "klee/ADT/RNG.h"
#include "klee/ADT/Ref.h"
#include "klee/Config/Version.h"
#include "klee/Core/Interpreter.h"
#include "klee/Expr/ArrayExprOptimizer.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Expr/ExprSMTLIBPrinter.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/KDAlloc/kdalloc.h"
#include "klee/Module/Cell.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KCallable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Solver/Common.h"
#include "klee/Solver/SolverCmdLine.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Specification/SpecificationManager.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Support/Casting.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"
#include "klee/Support/ModuleUtil.h"
#include "klee/Support/OptionCategories.h"
#include "klee/System/MemoryUsage.h"
#include "klee/System/Time.h"
#include "klee/Utils/llvm_related.h"
#include "klee/Utils/log.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include <cmath>
#include <cstddef>
#include <set>
#include <sys/types.h>
#include <utility>
#if LLVM_VERSION_CODE >= LLVM_VERSION(10, 0)
#include "llvm/Support/TypeSize.h"
#else
typedef unsigned TypeSize;
#endif
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cassert>
#include <cerrno>
#include <cstdint>
#include <cstring>
#include <cxxabi.h>
#include <fstream>
#include <iomanip>
#include <iosfwd>
#include <limits>
#include <sstream>
#include <string>
#include <sys/mman.h>
#include <sys/resource.h>
#include <vector>

using namespace llvm;
using namespace klee;

namespace klee {
cl::OptionCategory DebugCat("Debugging options",
                            "These are debugging options.");

cl::OptionCategory ExtCallsCat("External call policy options",
                               "These options impact external calls.");

cl::OptionCategory SeedingCat(
    "Seeding options",
    "These options are related to the use of seeds to start exploration.");

cl::OptionCategory
    TerminationCat("State and overall termination options",
                   "These options control termination of the overall KLEE "
                   "execution and of individual states.");

cl::OptionCategory TestGenCat("Test generation options",
                              "These options impact test generation.");

cl::opt<std::string>
    MaxTime("max-time",
            cl::desc("Halt execution after the specified duration.  "
                     "Set to 0s to disable (default=0s)"),
            cl::init("0s"), cl::cat(TerminationCat));
} // namespace klee

namespace {

/*** Test generation options ***/

cl::opt<bool> DumpStatesOnHalt(
    "dump-states-on-halt", cl::init(true),
    cl::desc("Dump test cases for all active states on exit (default=true)"),
    cl::cat(TestGenCat));

cl::opt<bool> OnlyOutputStatesCoveringNew(
    "only-output-states-covering-new", cl::init(false),
    cl::desc("Only output test cases covering new code (default=false)"),
    cl::cat(TestGenCat));

cl::opt<bool> EmitAllErrors(
    "emit-all-errors", cl::init(false),
    cl::desc("Generate tests cases for all errors "
             "(default=false, i.e. one per (error,instruction) pair)"),
    cl::cat(TestGenCat));

/* Constraint solving options */

cl::opt<unsigned> MaxSymArraySize(
    "max-sym-array-size",
    cl::desc(
        "If a symbolic array exceeds this size (in bytes), symbolic addresses "
        "into this array are concretized.  Set to 0 to disable (default=0)"),
    cl::init(0), cl::cat(SolvingCat));

// yuhao: init to true
cl::opt<bool>
    SimplifySymIndices("simplify-sym-indices", cl::init(true),
                       cl::desc("Simplify symbolic accesses using equalities "
                                "from other constraints (default=false)"),
                       cl::cat(SolvingCat));

cl::opt<bool>
    EqualitySubstitution("equality-substitution", cl::init(true),
                         cl::desc("Simplify equality expressions before "
                                  "querying the solver (default=true)"),
                         cl::cat(SolvingCat));

/*** External call policy options ***/

enum class ExternalCallPolicy {
  None,     // No external calls allowed
  Concrete, // Only external calls with concrete arguments allowed
  All,      // All external calls allowed
};

cl::opt<ExternalCallPolicy> ExternalCalls(
    "external-calls", cl::desc("Specify the external call policy"),
    cl::values(
        clEnumValN(
            ExternalCallPolicy::None, "none",
            "No external function calls are allowed.  Note that KLEE always "
            "allows some external calls with concrete arguments to go through "
            "(in particular printf and puts), regardless of this option."),
        clEnumValN(ExternalCallPolicy::Concrete, "concrete",
                   "Only external function calls with concrete arguments are "
                   "allowed (default)"),
        clEnumValN(ExternalCallPolicy::All, "all",
                   "All external function calls are allowed.  This concretizes "
                   "any symbolic arguments in calls to external functions.")),
    // yuhao: default=None
    cl::init(ExternalCallPolicy::None), cl::cat(ExtCallsCat));

cl::opt<bool> SuppressExternalWarnings(
    "suppress-external-warnings", cl::init(false),
    cl::desc("Supress warnings about calling external functions."),
    cl::cat(ExtCallsCat));

cl::opt<bool> AllExternalWarnings(
    "all-external-warnings", cl::init(false),
    cl::desc("Issue a warning everytime an external call is made, "
             "as opposed to once per function (default=false)"),
    cl::cat(ExtCallsCat));

cl::opt<std::size_t> ExternalPageThreshold(
    "kdalloc-external-page-threshold", cl::init(1024),
    cl::desc(
        "Threshold for garbage collecting pages used by external calls. If "
        "there is a significant number of infrequently used pages resident in "
        "memory, these will only be cleaned up if the total number of pages "
        "used for external calls is above the given threshold (default=1024)."),
    cl::cat(ExtCallsCat));

/*** Seeding options ***/

cl::opt<bool> AlwaysOutputSeeds(
    "always-output-seeds", cl::init(true),
    cl::desc(
        "Dump test cases even if they are driven by seeds only (default=true)"),
    cl::cat(SeedingCat));

cl::opt<bool> OnlyReplaySeeds(
    "only-replay-seeds", cl::init(false),
    cl::desc("Discard states that do not have a seed (default=false)."),
    cl::cat(SeedingCat));

cl::opt<bool> OnlySeed("only-seed", cl::init(false),
                       cl::desc("Stop execution after seeding is done without "
                                "doing regular search (default=false)."),
                       cl::cat(SeedingCat));

cl::opt<bool>
    AllowSeedExtension("allow-seed-extension", cl::init(false),
                       cl::desc("Allow extra (unbound) values to become "
                                "symbolic during seeding (default=false)."),
                       cl::cat(SeedingCat));

cl::opt<bool> ZeroSeedExtension(
    "zero-seed-extension", cl::init(false),
    cl::desc(
        "Use zero-filled objects if matching seed not found (default=false)"),
    cl::cat(SeedingCat));

cl::opt<bool> AllowSeedTruncation(
    "allow-seed-truncation", cl::init(false),
    cl::desc("Allow smaller buffers than in seeds (default=false)."),
    cl::cat(SeedingCat));

cl::opt<bool> NamedSeedMatching(
    "named-seed-matching", cl::init(false),
    cl::desc("Use names to match symbolic objects to inputs (default=false)."),
    cl::cat(SeedingCat));

cl::opt<std::string>
    SeedTime("seed-time",
             cl::desc("Amount of time to dedicate to seeds, before normal "
                      "search (default=0s (off))"),
             cl::cat(SeedingCat));

/*** Termination criteria options ***/

cl::list<StateTerminationType> ExitOnErrorType(
    "exit-on-error-type",
    cl::desc(
        "Stop execution after reaching a specified condition (default=false)"),
    cl::values(
        clEnumValN(StateTerminationType::Abort, "Abort",
                   "The program crashed (reached abort()/klee_abort())"),
        clEnumValN(StateTerminationType::Assert, "Assert",
                   "An assertion was hit"),
        clEnumValN(StateTerminationType::BadVectorAccess, "BadVectorAccess",
                   "Vector accessed out of bounds"),
        clEnumValN(StateTerminationType::Execution, "Execution",
                   "Trying to execute an unexpected instruction"),
        clEnumValN(StateTerminationType::External, "External",
                   "External objects referenced"),
        clEnumValN(StateTerminationType::Free, "Free",
                   "Freeing invalid memory"),
        clEnumValN(StateTerminationType::Model, "Model",
                   "Memory model limit hit"),
        clEnumValN(StateTerminationType::Overflow, "Overflow",
                   "An overflow occurred"),
        clEnumValN(StateTerminationType::Ptr, "Ptr", "Pointer error"),
        clEnumValN(StateTerminationType::ReadOnly, "ReadOnly",
                   "Write to read-only memory"),
        clEnumValN(StateTerminationType::ReportError, "ReportError",
                   "klee_report_error called"),
        clEnumValN(StateTerminationType::InvalidBuiltin, "InvalidBuiltin",
                   "Passing invalid value to compiler builtin"),
        clEnumValN(StateTerminationType::ImplicitTruncation,
                   "ImplicitTruncation",
                   "Implicit conversion from integer of larger bit width to "
                   "smaller bit width that results in data loss"),
        clEnumValN(StateTerminationType::ImplicitConversion,
                   "ImplicitConversion",
                   "Implicit conversion between integer types that changes the "
                   "sign of the value"),
        clEnumValN(StateTerminationType::UnreachableCall, "UnreachableCall",
                   "Control flow reached an unreachable program point"),
        clEnumValN(StateTerminationType::MissingReturn, "MissingReturn",
                   "Reaching the end of a value-returning function without "
                   "returning a value"),
        clEnumValN(StateTerminationType::InvalidLoad, "InvalidLoad",
                   "Load of a value which is not in the range of representable "
                   "values for that type"),
        clEnumValN(StateTerminationType::NullableAttribute, "NullableAttribute",
                   "Violation of nullable attribute detected"),
        clEnumValN(StateTerminationType::User, "User",
                   "Wrong klee_* functions invocation")),
    cl::ZeroOrMore, cl::cat(TerminationCat));

cl::opt<unsigned long long>
    MaxInstructions("max-instructions",
                    cl::desc("Stop execution after this many instructions.  "
                             "Set to 0 to disable (default=0)"),
                    cl::init(0), cl::cat(TerminationCat));

cl::opt<unsigned> MaxForks(
    "max-forks",
    cl::desc("Only fork this many times.  Set to -1 to disable (default=-1)"),
    cl::init(~0u), cl::cat(TerminationCat));

cl::opt<unsigned> MaxDepth("max-depth",
                           cl::desc("Only allow this many symbolic branches.  "
                                    "Set to 0 to disable (default=0)"),
                           cl::init(0), cl::cat(TerminationCat));

cl::opt<unsigned>
    MaxMemory("max-memory",
              cl::desc("Refuse to fork when above this amount of "
                       "memory (in MB) (see -max-memory-inhibit) and terminate "
                       "states when additional 100MB allocated (default=2000)"),
              // yuhao: default=100000
              cl::init(100000), cl::cat(TerminationCat));

cl::opt<bool> MaxMemoryInhibit("max-memory-inhibit",
                               cl::desc("Inhibit forking when above memory cap "
                                        "(see -max-memory) (default=true)"),
                               cl::init(true), cl::cat(TerminationCat));

cl::opt<unsigned> RuntimeMaxStackFrames(
    "max-stack-frames",
    cl::desc("Terminate a state after this many stack frames.  Set to 0 to "
             "disable (default=8192)"),
    // yuhao: default=64
    cl::init(64), cl::cat(TerminationCat));

cl::opt<double> MaxStaticForkPct(
    "max-static-fork-pct", cl::init(1.),
    cl::desc("Maximum percentage spent by an instruction forking out of the "
             "forking of all instructions (default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticSolvePct(
    "max-static-solve-pct", cl::init(1.),
    cl::desc("Maximum percentage of solving time that can be spent by a single "
             "instruction over total solving time for all instructions "
             "(default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticCPForkPct(
    "max-static-cpfork-pct", cl::init(1.),
    cl::desc("Maximum percentage spent by an instruction of a call path "
             "forking out of the forking of all instructions in the call path "
             "(default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<double> MaxStaticCPSolvePct(
    "max-static-cpsolve-pct", cl::init(1.),
    cl::desc("Maximum percentage of solving time that can be spent by a single "
             "instruction of a call path over total solving time for all "
             "instructions (default=1.0 (always))"),
    cl::cat(TerminationCat));

cl::opt<unsigned> MaxStaticPctCheckDelay(
    "max-static-pct-check-delay",
    cl::desc("Number of forks after which the --max-static-*-pct checks are "
             "enforced (default=1000)"),
    cl::init(1000), cl::cat(TerminationCat));

cl::opt<std::string> TimerInterval(
    "timer-interval",
    cl::desc(
        "Minimum interval to check timers. "
        "Affects -max-time, -istats-write-interval, -stats-write-interval, and "
        "-uncovered-update-interval (default=1s)"),
    cl::init("1s"), cl::cat(TerminationCat));

/*** Debugging options ***/

/// The different query logging solvers that can switched on/off
enum PrintDebugInstructionsType {
  STDERR_ALL, ///
  STDERR_SRC,
  STDERR_COMPACT,
  FILE_ALL,    ///
  FILE_SRC,    ///
  FILE_COMPACT ///
};

llvm::cl::bits<PrintDebugInstructionsType> DebugPrintInstructions(
    "debug-print-instructions",
    llvm::cl::desc("Log instructions during execution."),
    llvm::cl::values(
        clEnumValN(STDERR_ALL, "all:stderr",
                   "Log all instructions to stderr "
                   "in format [src, inst_id, "
                   "llvm_inst]"),
        clEnumValN(STDERR_SRC, "src:stderr",
                   "Log all instructions to stderr in format [src, inst_id]"),
        clEnumValN(STDERR_COMPACT, "compact:stderr",
                   "Log all instructions to stderr in format [inst_id]"),
        clEnumValN(FILE_ALL, "all:file",
                   "Log all instructions to file "
                   "instructions.txt in format [src, "
                   "inst_id, llvm_inst]"),
        clEnumValN(FILE_SRC, "src:file",
                   "Log all instructions to file "
                   "instructions.txt in format [src, "
                   "inst_id]"),

        clEnumValN(FILE_COMPACT, "compact:file",
                   "Log all instructions to file instructions.txt in format "
                   "[inst_id]")),
    llvm::cl::CommaSeparated, cl::cat(DebugCat));

#ifdef HAVE_ZLIB_H
cl::opt<bool> DebugCompressInstructions(
    "debug-compress-instructions", cl::init(false),
    cl::desc(
        "Compress the logged instructions in gzip format (default=false)."),
    cl::cat(DebugCat));
#endif

cl::opt<bool> DebugCheckForImpliedValues(
    "debug-check-for-implied-values", cl::init(false),
    cl::desc("Debug the implied value optimization"), cl::cat(DebugCat));

} // namespace

// XXX hack
extern "C" unsigned dumpStates, dumpPTree;
unsigned dumpStates = 0, dumpPTree = 0;

Executor::Executor(LLVMContext &ctx, const InterpreterOptions &opts,
                   InterpreterHandler *ih)
    : Interpreter(opts), interpreterHandler(ih), searcher(0),
      externalDispatcher(new ExternalDispatcher(ctx)), statsTracker(0),
      pathWriter(0), symPathWriter(0),
      specialFunctionHandler(0), timers{time::Span(TimerInterval)},
      replayKTest(0), replayPath(0), usingSeeds(0), atMemoryLimit(false),
      inhibitForking(false), haltExecution(false), ivcEnabled(false),
      debugLogBuffer(debugBufferString) {

  const time::Span maxTime{MaxTime};
  if (maxTime)
    timers.add(std::make_unique<Timer>(maxTime, [&] {
      klee_message("HaltTimer invoked");
      setHaltExecution(true);
    }));

  coreSolverTimeout = time::Span{MaxCoreSolverTime};
  if (coreSolverTimeout)
    UseForkedCoreSolver = true;
  std::unique_ptr<Solver> coreSolver = klee::createCoreSolver(CoreSolverToUse);
  if (!coreSolver) {
    klee_error("Failed to create core solver\n");
  }

  std::unique_ptr<Solver> solver = constructSolverChain(
      std::move(coreSolver),
      interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(ALL_QUERIES_KQUERY_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_KQUERY_FILE_NAME));

  this->solver =
      std::make_unique<TimingSolver>(std::move(solver), EqualitySubstitution);
  memory = std::make_unique<MemoryManager>(&arrayCache);

  initializeSearchOptions();

  if (OnlyOutputStatesCoveringNew && !StatsTracker::useIStats())
    klee_error("To use --only-output-states-covering-new, you need to enable "
               "--output-istats.");

  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    std::string debug_file_name =
        interpreterHandler->getOutputFilename("instructions.txt");
    std::string error;
#ifdef HAVE_ZLIB_H
    if (!DebugCompressInstructions) {
#endif
      debugInstFile = klee_open_output_file(debug_file_name, error);
#ifdef HAVE_ZLIB_H
    } else {
      debug_file_name.append(".gz");
      debugInstFile = klee_open_compressed_output_file(debug_file_name, error);
    }
#endif
    if (!debugInstFile) {
      klee_error("Could not open file %s : %s", debug_file_name.c_str(),
                 error.c_str());
    }
  }

  // yuhao:
  spec_manager.spec_config = &this->spec_config;
}

llvm::Module *
Executor::setModule(std::vector<std::unique_ptr<llvm::Module>> &modules,
                    const ModuleOptions &opts) {
  assert(!kmodule && !modules.empty() &&
         "can only register one module"); // XXX gross

  kmodule = std::unique_ptr<KModule>(new KModule());

  // Preparing the final module happens in multiple stages

  // yuhao: under constrained symbolic execution for kernel do not need this
  // Link with KLEE intrinsics library before running any optimizations
  // SmallString<128> LibPath(opts.LibraryDir);
  // llvm::sys::path::append(LibPath,
  //                         "libkleeRuntimeIntrinsic" + opts.OptSuffix +
  //                         ".bca");
  // std::string error;
  // if (!klee::loadFile(LibPath.c_str(), modules[0]->getContext(), modules,
  //                     error)) {
  //   klee_error("Could not load KLEE intrinsic file %s", LibPath.c_str());
  // }

  // 1.) Link the modules together
  while (kmodule->link(modules, opts.EntryPoint)) {
    // 2.) Apply different instrumentation
    kmodule->instrument(opts);
  }

  // 3.) Optimise and prepare for KLEE

  // Create a list of functions that should be preserved if used
  std::vector<const char *> preservedFunctions;
  specialFunctionHandler = new SpecialFunctionHandler(*this);
  specialFunctionHandler->prepare(preservedFunctions);

  preservedFunctions.push_back(opts.EntryPoint.c_str());

  // Preserve the free-standing library calls
  preservedFunctions.push_back("memset");
  preservedFunctions.push_back("memcpy");
  preservedFunctions.push_back("memcmp");
  preservedFunctions.push_back("memmove");

  kmodule->optimiseAndPrepare(opts, preservedFunctions);
  kmodule->checkModule();

  // 4.) Manifest the module
  kmodule->manifest(interpreterHandler, StatsTracker::useStatistics());

  specialFunctionHandler->bind();

  if (StatsTracker::useStatistics() || userSearcherRequiresMD2U()) {
    statsTracker = new StatsTracker(
        *this, interpreterHandler->getOutputFilename("assembly.ll"),
        userSearcherRequiresMD2U());
  }

  // Initialize the context.
  DataLayout *TD = kmodule->targetData.get();
  Context::initialize(TD->isLittleEndian(),
                      (Expr::Width)TD->getPointerSizeInBits());

  return kmodule->module.get();
}

Executor::~Executor() {
  delete externalDispatcher;
  delete specialFunctionHandler;
  delete statsTracker;
}

/***/

void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
                                      const llvm::Value *v, const Constant *c,
                                      unsigned offset,
                                      // yuhao:
                                      bool symbolic) {
  const auto targetData = kmodule->targetData.get();
  if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
    unsigned elementSize =
        targetData->getTypeStoreSize(cp->getType()->getElementType());
    for (unsigned i = 0, e = cp->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, v, cp->getOperand(i),
                             offset + i * elementSize);
  } else if (isa<ConstantAggregateZero>(c)) {
    unsigned i, size = targetData->getTypeStoreSize(c->getType());
    for (i = 0; i < size; i++)
      os->write8(offset + i, (uint8_t)0);

    // yuhao:
    if (symbolic) {
      // hy_log(-1, "ConstantAggregateZero");
      // hy_dump(-1, c->print, str);
      auto ty = c->getType();
      // hy_dump(-1, ty->print, str);
      initializeGlobalObject(state, os, v, ty, offset, true);
    }

  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
    unsigned elementSize =
        targetData->getTypeStoreSize(ca->getType()->getElementType());
    for (unsigned i = 0, e = ca->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, v, ca->getOperand(i),
                             offset + i * elementSize);
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
    const StructLayout *sl =
        targetData->getStructLayout(cast<StructType>(cs->getType()));
    for (unsigned i = 0, e = cs->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, v, cs->getOperand(i),
                             offset + sl->getElementOffset(i));
  } else if (const ConstantDataSequential *cds =
                 dyn_cast<ConstantDataSequential>(c)) {
    unsigned elementSize = targetData->getTypeStoreSize(cds->getElementType());
    for (unsigned i = 0, e = cds->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, v, cds->getElementAsConstant(i),
                             offset + i * elementSize);
  } else if (!isa<UndefValue>(c) && !isa<MetadataAsValue>(c)) {
    unsigned StoreBits = targetData->getTypeStoreSizeInBits(c->getType());
    ref<ConstantExpr> C = evalConstant(c);

    // Extend the constant if necessary;
    assert(StoreBits >= C->getWidth() && "Invalid store size!");
    if (StoreBits > C->getWidth())
      C = C->ZExt(StoreBits);

    os->write(offset, C);
  }
}

// yuhao:
void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
                                      const llvm::Value *v, llvm::Type *ty,
                                      unsigned offset, bool only_pointer) {
  const auto targetData = kmodule->targetData.get();
  if (auto *vt = dyn_cast<VectorType>(ty)) {
    unsigned elementSize = targetData->getTypeStoreSize(vt->getElementType());
    for (unsigned i = 0, e = vt->getNumContainedTypes(); i != e; ++i)
      initializeGlobalObject(state, os, v, vt->getElementType(),
                             offset + i * elementSize);
  } else if (auto *at = dyn_cast<ArrayType>(ty)) {
    unsigned elementSize = targetData->getTypeStoreSize(at->getElementType());
    for (unsigned i = 0, e = at->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, v, at->getElementType(),
                             offset + i * elementSize);
  } else if (auto *st = dyn_cast<StructType>(ty)) {
    const StructLayout *sl = targetData->getStructLayout(st);
    for (unsigned i = 0, e = st->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, v, st->getElementType(i),
                             offset + sl->getElementOffset(i));
  } else if (auto *pt = dyn_cast<PointerType>(ty)) {
    if (only_pointer) {
      std::string str;
      hy_log(-1, "pt:");
      hy_dump(-1, pt->print, str);
    }

    std::string name = get_global_name();
    unsigned int size = kmodule->targetData->getTypeStoreSize(pt);
    Expr::Width width = getWidthForLLVMType(pt);
    auto expr = manual_make_symbolic(state, name, v, size, width, pt);
    os->write(offset, expr);
  } else if (auto *it = dyn_cast<IntegerType>(ty)) {
    if (only_pointer) {
      return;
    }

    std::string name = get_global_name();
    unsigned int size = kmodule->targetData->getTypeStoreSize(it);
    Expr::Width width = getWidthForLLVMType(it);
    auto expr = manual_make_symbolic(state, name, v, size, width, ty);
    os->write(offset, expr);
  } else {
    std::string str = "error type in initializeGlobalObject(): ";
    hy_add(3, ty->print, str);
    assert(0 && str.c_str());
  }
}

MemoryObject *Executor::addExternalObject(ExecutionState &state, void *addr,
                                          unsigned size, bool isReadOnly) {
  auto mo = memory->allocateFixed(reinterpret_cast<std::uint64_t>(addr), size,
                                  nullptr);
  ObjectState *os = bindObjectInState(state, mo, false);
  for (unsigned i = 0; i < size; i++)
    os->write8(i, ((uint8_t *)addr)[i]);
  if (isReadOnly)
    os->setReadOnly(true);
  return mo;
}

extern void *__dso_handle __attribute__((__weak__));

void Executor::initializeGlobals(ExecutionState &state) {
  // allocate and initialize globals, done in two passes since we may
  // need address of a global in order to initialize some other one.

  // allocate memory objects for all globals
  allocateGlobalObjects(state);

  // initialize aliases first, may be needed for global objects
  initializeGlobalAliases();

  // finally, do the actual initialization
  initializeGlobalObjects(state);
}

void Executor::allocateGlobalObjects(ExecutionState &state) {
  Module *m = kmodule->module.get();

  if (m->getModuleInlineAsm() != "")
    klee_warning("executable has module level assembly (ignoring)");
  // represent function globals using the address of the actual llvm function
  // object. given that we use malloc to allocate memory in states this also
  // ensures that we won't conflict. we don't need to allocate a memory object
  // since reading/writing via a function pointer is unsupported anyway.
  for (Function &f : *m) {
    ref<ConstantExpr> addr;

    // If the symbol has external weak linkage then it is implicitly
    // not defined in this module; if it isn't resolvable then it
    // should be null.
    if (f.hasExternalWeakLinkage() &&
        !externalDispatcher->resolveSymbol(f.getName().str())) {
      addr = Expr::createPointer(0);
    } else {
      // We allocate an object to represent each function,
      // its address can be used for function pointers.
      // TODO: Check whether the object is accessed?
      auto mo = memory->allocate(8, false, true, &state, &f, 8);
      // yuhao: set type for functions
      add_mo_type(state, mo, f.getFunctionType());
      //      std::string str;
      //      mo->getAllocInfo(str);
      //      hy_log(-1, str);

      addr = Expr::createPointer(mo->address);
      legalFunctions.emplace(mo->address, &f);
      legalFunctionsAddress.emplace(&f, mo->address);
    }

    globalAddresses.emplace(&f, addr);
  }

#ifndef WINDOWS
  int *errno_addr = getErrnoLocation(state);
  MemoryObject *errnoObj =
      addExternalObject(state, (void *)errno_addr, sizeof *errno_addr, false);
  // Copy values from and to program space explicitly
  errnoObj->isUserSpecified = true;
#endif

  // Disabled, we don't want to promote use of live externals.
#ifdef HAVE_CTYPE_EXTERNALS
#ifndef WINDOWS
#ifndef DARWIN
  /* from /usr/include/ctype.h:
       These point into arrays of 384, so they can be indexed by any `unsigned
       char' value [0,255]; by EOF (-1); or by any `signed char' value
       [-128,-1).  ISO C requires that the ctype functions work for `unsigned */
  const uint16_t **addr = __ctype_b_loc();
  addExternalObject(state, const_cast<uint16_t *>(*addr - 128),
                    384 * sizeof **addr, true);
  addExternalObject(state, addr, sizeof(*addr), true);

  const int32_t **lower_addr = __ctype_tolower_loc();
  addExternalObject(state, const_cast<int32_t *>(*lower_addr - 128),
                    384 * sizeof **lower_addr, true);
  addExternalObject(state, lower_addr, sizeof(*lower_addr), true);

  const int32_t **upper_addr = __ctype_toupper_loc();
  addExternalObject(state, const_cast<int32_t *>(*upper_addr - 128),
                    384 * sizeof **upper_addr, true);
  addExternalObject(state, upper_addr, sizeof(*upper_addr), true);
#endif
#endif
#endif

  for (const GlobalVariable &v : m->globals()) {
    std::size_t globalObjectAlignment = getAllocationAlignment(&v);
    Type *ty = v.getValueType();
    std::uint64_t size = 0;
    if (ty->isSized())
      size = kmodule->targetData->getTypeStoreSize(ty);

    if (v.isDeclaration()) {
      // FIXME: We have no general way of handling unknown external
      // symbols. If we really cared about making external stuff work
      // better we could support user definition, or use the EXE style
      // hack where we check the object file information.

      if (!ty->isSized()) {
        klee_warning("Type for %.*s is not sized",
                     static_cast<int>(v.getName().size()), v.getName().data());
      }

      // XXX - DWD - hardcode some things until we decide how to fix.
#ifndef WINDOWS
      if (v.getName() == "_ZTVN10__cxxabiv117__class_type_infoE") {
        size = 0x2C;
      } else if (v.getName() == "_ZTVN10__cxxabiv120__si_class_type_infoE") {
        size = 0x2C;
      } else if (v.getName() == "_ZTVN10__cxxabiv121__vmi_class_type_infoE") {
        size = 0x2C;
      }
#endif

      if (size == 0) {
        klee_warning("Unable to find size for global variable: %.*s (use will "
                     "result in out of bounds access)",
                     static_cast<int>(v.getName().size()), v.getName().data());
      }
    }

    MemoryObject *mo = memory->allocate(size, /*isLocal=*/false,
                                        /*isGlobal=*/true, /*state=*/nullptr,
                                        /*allocSite=*/&v,
                                        /*alignment=*/globalObjectAlignment);
    if (!mo)
      klee_error("out of memory");

    // yuhao: set type for global variables
    add_mo_type(state, mo, ty);

    globalObjects.emplace(&v, mo);
    globalAddresses.emplace(&v, mo->getBaseExpr());
  }
}

void Executor::initializeGlobalAlias(const llvm::Constant *c) {
  // aliasee may either be a global value or constant expression
  const auto *ga = dyn_cast<GlobalAlias>(c);
  if (ga) {
    if (globalAddresses.count(ga)) {
      // already resolved by previous invocation
      return;
    }
    const llvm::Constant *aliasee = ga->getAliasee();
    if (const auto *gv = dyn_cast<GlobalValue>(aliasee)) {
      // aliasee is global value
      auto it = globalAddresses.find(gv);
      // uninitialized only if aliasee is another global alias
      if (it != globalAddresses.end()) {
        globalAddresses.emplace(ga, it->second);
        return;
      }
    }
  }

  // resolve aliases in all sub-expressions
  for (const auto *op : c->operand_values()) {
    initializeGlobalAlias(cast<Constant>(op));
  }

  if (ga) {
    // aliasee is constant expression (or global alias)
    globalAddresses.emplace(ga, evalConstant(ga->getAliasee()));
  }
}

void Executor::initializeGlobalAliases() {
  const Module *m = kmodule->module.get();
  for (const GlobalAlias &a : m->aliases()) {
    initializeGlobalAlias(&a);
  }
}

void Executor::initializeGlobalObjects(ExecutionState &state) {
  const Module *m = kmodule->module.get();

  for (const GlobalVariable &v : m->globals()) {
    MemoryObject *mo = globalObjects.find(&v)->second;
    ObjectState *os = bindObjectInState(state, mo, false);

    // yuhao: not handle external global variables
    if (v.isExternallyInitialized()) {

      // } else if (v.isDeclaration() && mo->size) {
      //   // Program already running -> object already initialized.
      //   // Read concrete value and write it to our copy.

      //   // yuhao: not handle declaration global variables
      //   void *addr;
      //   if (v.getName() == "__dso_handle") {
      //     addr = &__dso_handle; // wtf ?
      //   } else {
      //     addr = externalDispatcher->resolveSymbol(v.getName().str());
      //   }
      //   if (!addr) {
      //     klee_error("Unable to load symbol(%.*s) while initializing
      //     globals",
      //                static_cast<int>(v.getName().size()),
      //                v.getName().data());
      //   }
      //   for (unsigned offset = 0; offset < mo->size; offset++) {
      //     os->write8(offset, static_cast<unsigned char *>(addr)[offset]);
      //   }
    } else if (v.hasInitializer()) {

      // yuhao: set the value for null pointers in global variables with name
      std::string str;
      bool symbolic = (!v.isConstant()) && v.hasName();
      //      if (symbolic) {
      //        hy_log(-1, "name: " + v.getName().str());
      //        hy_log(-1, "v.getInitializer():");
      //        hy_dump(-1, v.getInitializer()->print, str);
      //        hy_log(-1, "v.getType():");
      //        hy_dump(-1, v.getType()->print, str);
      //      }
      current_global_name = v.getName().str();
      initializeGlobalObject(state, os, &v, v.getInitializer(), 0, symbolic);

      if (v.isConstant()) {
        os->setReadOnly(true);
        // initialise constant memory that may be used with external calls
        state.addressSpace.copyOutConcrete(mo, os);
      }
    } else {
      // yuhao:
      // os->initializeToRandom();
      os->initializeToZero();
      // initialize global object with symbolic value
      current_global_name = v.getName().str();
      initializeGlobalObject(state, os, &v,
                             v.getType()->getPointerElementType(), 0);
    }
  }
}

bool Executor::branchingPermitted(const ExecutionState &state) const {
  if ((MaxMemoryInhibit && atMemoryLimit) || state.forkDisabled ||
      inhibitForking || (MaxForks != ~0u && stats::forks >= MaxForks)) {

    if (MaxMemoryInhibit && atMemoryLimit)
      klee_warning_once(0, "skipping fork (memory cap exceeded)");
    else if (state.forkDisabled)
      klee_warning_once(0, "skipping fork (fork disabled on current path)");
    else if (inhibitForking)
      klee_warning_once(0, "skipping fork (fork disabled globally)");
    else
      klee_warning_once(0, "skipping fork (max-forks reached)");

    return false;
  }

  return true;
}

void Executor::branch(ExecutionState &state,
                      const std::vector<ref<Expr>> &conditions,
                      std::vector<ExecutionState *> &result,
                      BranchType reason) {
  TimerStatIncrementer timer(stats::forkTime);
  unsigned N = conditions.size();
  assert(N);

  if (!branchingPermitted(state)) {
    unsigned next = theRNG.getInt32() % N;
    for (unsigned i = 0; i < N; ++i) {
      if (i == next) {
        result.push_back(&state);
      } else {
        result.push_back(nullptr);
      }
    }
    stats::inhibitedForks += N - 1;
  } else {
    stats::forks += N - 1;
    stats::incBranchStat(reason, N - 1);

    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i = 1; i < N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      addedStates.push_back(ns);
      result.push_back(ns);
      processTree->attach(es->ptreeNode, ns, es, reason);
    }
  }

  // If necessary redistribute seeds to match conditions, killing
  // states if necessary due to OnlyReplaySeeds (inefficient but
  // simple).

  std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
      seedMap.find(&state);
  if (it != seedMap.end()) {
    std::vector<SeedInfo> seeds = it->second;
    seedMap.erase(it);

    // Assume each seed only satisfies one condition (necessarily true
    // when conditions are mutually exclusive and their conjunction is
    // a tautology).
    for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
                                         siie = seeds.end();
         siit != siie; ++siit) {
      unsigned i;
      for (i = 0; i < N; ++i) {
        ref<ConstantExpr> res;
        solver->setTimeout(coreSolverTimeout);
        bool success = solver->getValue(
            state.constraints, siit->assignment.evaluate(conditions[i]), res,
            state.queryMetaData);
        solver->setTimeout(time::Span());

        // yuhao:
        // assert(success && "FIXME: Unhandled solver failure");
        if (!success) {
          res = siit->assignment.evaluate(conditions[i]);
        }

        (void)success;
        if (res->isTrue())
          break;
      }

      // If we didn't find a satisfying condition randomly pick one
      // (the seed will be patched).
      if (i == N)
        i = theRNG.getInt32() % N;

      // Extra check in case we're replaying seeds with a max-fork
      if (result[i])
        seedMap[result[i]].push_back(*siit);
    }

    if (OnlyReplaySeeds) {
      for (unsigned i = 0; i < N; ++i) {
        if (result[i] && !seedMap.count(result[i])) {
          terminateStateEarlyAlgorithm(*result[i],
                                       "Unseeded path during replay",
                                       StateTerminationType::Replay);
          result[i] = nullptr;
        }
      }
    }
  }

  for (unsigned i = 0; i < N; ++i)
    if (result[i])
      addConstraint(*result[i], conditions[i]);
}

ref<Expr> Executor::maxStaticPctChecks(ExecutionState &current,
                                       ref<Expr> condition) {
  if (isa<klee::ConstantExpr>(condition))
    return condition;

  if (MaxStaticForkPct == 1. && MaxStaticSolvePct == 1. &&
      MaxStaticCPForkPct == 1. && MaxStaticCPSolvePct == 1.)
    return condition;

  // These checks are performed only after at least MaxStaticPctCheckDelay forks
  // have been performed since execution started
  if (stats::forks < MaxStaticPctCheckDelay)
    return condition;

  StatisticManager &sm = *theStatisticManager;
  CallPathNode *cpn = current.stack.back().callPathNode;

  bool reached_max_fork_limit =
      (MaxStaticForkPct < 1. &&
       (sm.getIndexedValue(stats::forks, sm.getIndex()) >
        stats::forks * MaxStaticForkPct));

  bool reached_max_cp_fork_limit = (MaxStaticCPForkPct < 1. && cpn &&
                                    (cpn->statistics.getValue(stats::forks) >
                                     stats::forks * MaxStaticCPForkPct));

  bool reached_max_solver_limit =
      (MaxStaticSolvePct < 1 &&
       (sm.getIndexedValue(stats::solverTime, sm.getIndex()) >
        stats::solverTime * MaxStaticSolvePct));

  bool reached_max_cp_solver_limit =
      (MaxStaticCPForkPct < 1. && cpn &&
       (cpn->statistics.getValue(stats::solverTime) >
        stats::solverTime * MaxStaticCPSolvePct));

  if (reached_max_fork_limit || reached_max_cp_fork_limit ||
      reached_max_solver_limit || reached_max_cp_solver_limit) {
    ref<klee::ConstantExpr> value;
    solver->setTimeout(coreSolverTimeout);
    bool success = solver->getValue(current.constraints, condition, value,
                                    current.queryMetaData);
    solver->setTimeout(time::Span());

    // yuhao:
    // assert(success && "FIXME: Unhandled solver failure");
    if (!success) {
      return condition;
    }

    (void)success;

    std::string msg("skipping fork and concretizing condition (MaxStatic*Pct "
                    "limit reached) at ");
    llvm::raw_string_ostream os(msg);
    os << current.prevPC->getSourceLocation();
    klee_warning_once(0, "%s", os.str().c_str());

    addConstraint(current, EqExpr::create(value, condition));
    condition = value;
  }
  return condition;
}

Executor::StatePair Executor::fork(ExecutionState &current, ref<Expr> condition,
                                   bool isInternal, BranchType reason) {
  Solver::Validity res;
  std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
      seedMap.find(&current);
  bool isSeeding = it != seedMap.end();

  if (!isSeeding)
    condition = maxStaticPctChecks(current, condition);

  time::Span timeout = coreSolverTimeout;
  if (isSeeding)
    timeout *= static_cast<unsigned>(it->second.size());
  solver->setTimeout(timeout);

  // yuhao:
  bool success = solver->evaluate(*current.ucmo_constraints, condition, res,
                                  current.queryMetaData);

  solver->setTimeout(time::Span());
  if (!success) {
    current.pc = current.prevPC;
    terminateStateOnSolverError(current, "Query timed out (fork).");
    return StatePair(nullptr, nullptr);
  }

  if (!isSeeding) {
    if (replayPath && !isInternal) {
      assert(replayPosition < replayPath->size() &&
             "ran out of branches in replay path mode");
      bool branch = (*replayPath)[replayPosition++];

      if (res == Solver::True) {
        assert(branch && "hit invalid branch in replay path mode");
      } else if (res == Solver::False) {
        assert(!branch && "hit invalid branch in replay path mode");
      } else {
        // add constraints
        if (branch) {
          res = Solver::True;
          addConstraint(current, condition);
        } else {
          res = Solver::False;
          addConstraint(current, Expr::createIsZero(condition));
        }
      }
    } else if (res == Solver::Unknown) {
      assert(!replayKTest && "in replay mode, only one branch can be true.");

      if (!branchingPermitted(current)) {
        TimerStatIncrementer timer(stats::forkTime);
        if (theRNG.getBool()) {
          addConstraint(current, condition);
          res = Solver::True;
        } else {
          addConstraint(current, Expr::createIsZero(condition));
          res = Solver::False;
        }
        ++stats::inhibitedForks;
      }
    }
  }

  // Fix branch in only-replay-seed mode, if we don't have both true
  // and false seeds.
  if (isSeeding && (current.forkDisabled || OnlyReplaySeeds) &&
      res == Solver::Unknown) {
    bool trueSeed = false, falseSeed = false;
    // Is seed extension still ok here?
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
                                         siie = it->second.end();
         siit != siie; ++siit) {
      ref<ConstantExpr> res;

      // yuhao:
      solver->setTimeout(coreSolverTimeout);
      bool success = solver->getValue(*current.ucmo_constraints,
                                      siit->assignment.evaluate(condition), res,
                                      current.queryMetaData);
      solver->setTimeout(time::Span());
      // assert(success && "FIXME: Unhandled solver failure");
      if (!success) {
        res = siit->assignment.evaluate(condition);
      }

      (void)success;
      if (res->isTrue()) {
        trueSeed = true;
      } else {
        falseSeed = true;
      }
      if (trueSeed && falseSeed)
        break;
    }
    if (!(trueSeed && falseSeed)) {
      assert(trueSeed || falseSeed);

      res = trueSeed ? Solver::True : Solver::False;
      addConstraint(current,
                    trueSeed ? condition : Expr::createIsZero(condition));
    }
  }

  // XXX - even if the constraint is provable one way or the other we
  // can probably benefit by adding this constraint and allowing it to
  // reduce the other constraints. For example, if we do a binary
  // search on a particular value, and then see a comparison against
  // the value it has been fixed at, we should take this as a nice
  // hint to just use the single constraint instead of all the binary
  // search ones. If that makes sense.
  if (res == Solver::True) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "1";
      }
    }

    return StatePair(&current, nullptr);
  } else if (res == Solver::False) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "0";
      }
    }

    return StatePair(nullptr, &current);
  } else {
    TimerStatIncrementer timer(stats::forkTime);
    ExecutionState *falseState, *trueState = &current;

    ++stats::forks;

    falseState = trueState->branch();
    addedStates.push_back(falseState);

    if (it != seedMap.end()) {
      std::vector<SeedInfo> seeds = it->second;
      it->second.clear();
      std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
      std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
      for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
                                           siie = seeds.end();
           siit != siie; ++siit) {
        ref<ConstantExpr> res;

        // yuhao:
        solver->setTimeout(coreSolverTimeout);
        bool success = solver->getValue(*current.ucmo_constraints,
                                        siit->assignment.evaluate(condition),
                                        res, current.queryMetaData);
        solver->setTimeout(time::Span());
        // assert(success && "FIXME: Unhandled solver failure");
        if (!success) {
          res = siit->assignment.evaluate(condition);
        }

        (void)success;
        if (res->isTrue()) {
          trueSeeds.push_back(*siit);
        } else {
          falseSeeds.push_back(*siit);
        }
      }

      bool swapInfo = false;
      if (trueSeeds.empty()) {
        if (&current == trueState)
          swapInfo = true;
        seedMap.erase(trueState);
      }
      if (falseSeeds.empty()) {
        if (&current == falseState)
          swapInfo = true;
        seedMap.erase(falseState);
      }
      if (swapInfo) {
        std::swap(trueState->coveredNew, falseState->coveredNew);
        std::swap(trueState->coveredLines, falseState->coveredLines);
      }
    }

    processTree->attach(current.ptreeNode, falseState, trueState, reason);
    stats::incBranchStat(reason, 1);

    if (pathWriter) {
      // Need to update the pathOS.id field of falseState, otherwise the same id
      // is used for both falseState and trueState.
      falseState->pathOS = pathWriter->open(current.pathOS);
      if (!isInternal) {
        trueState->pathOS << "1";
        falseState->pathOS << "0";
      }
    }
    if (symPathWriter) {
      falseState->symPathOS = symPathWriter->open(current.symPathOS);
      if (!isInternal) {
        trueState->symPathOS << "1";
        falseState->symPathOS << "0";
      }
    }

    addConstraint(*trueState, condition);
    addConstraint(*falseState, Expr::createIsZero(condition));

    // Kinda gross, do we even really still want this option?
    if (MaxDepth && MaxDepth <= trueState->depth) {
      terminateStateEarly(*trueState, "max-depth exceeded.",
                          StateTerminationType::MaxDepth);
      terminateStateEarly(*falseState, "max-depth exceeded.",
                          StateTerminationType::MaxDepth);
      return StatePair(nullptr, nullptr);
    }

    // yuhao: debug
    std::string str;
    uint64_t debug = 1;
    hy_log(debug, "fork at: " + dump_inst(current.prevPC->inst));
    hy_dump(-1, current.prevPC->inst->print, str);
    hy_print(debug, condition->print, str);
    // hy_log(debug, "cond is: " + str);
    hy_log(debug, "trueState is: " + std::to_string(trueState->getID()));
    hy_log(debug, "falseState is: " + std::to_string(falseState->getID()));

    return StatePair(trueState, falseState);
  }
}

void Executor::addConstraint(ExecutionState &state, ref<Expr> condition) {

  // yuhao: debug
  std::string str;
  hy_log(-1, "state: " + std::to_string(state.getID()) + " add constraint:");
  hy_dump(-1, state.pc->inst->print, str);
  hy_dump(-1, condition->print, str);

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }

  // Check to see if this constraint violates seeds.
  std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
      seedMap.find(&state);
  if (it != seedMap.end()) {
    bool warn = false;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
                                         siie = it->second.end();
         siit != siie; ++siit) {
      bool res;
      solver->setTimeout(coreSolverTimeout);
      bool success = solver->mustBeFalse(state.constraints,
                                         siit->assignment.evaluate(condition),
                                         res, state.queryMetaData);
      solver->setTimeout(time::Span());

      // yuhao:
      // assert(success && "FIXME: Unhandled solver failure");
      if (!success) {
        res = siit->assignment.evaluate(condition)->isFalse();
      }

      (void)success;
      if (res) {
        siit->patchSeed(state, condition, solver.get());
        warn = true;
      }
    }
    if (warn)
      klee_warning("seeds patched for violating constraint");
  }

  state.addConstraint(condition);
  if (ivcEnabled)
    doImpliedValueConcretization(state, condition,
                                 ConstantExpr::alloc(1, Expr::Bool));
}

const Cell &Executor::eval(KInstruction *ki, unsigned index,
                           ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  // yuhao:
  // assert(vnumber != -1 &&
  //        "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  // yuhao:
  if (vnumber == -1) {
    klee_message("vnumber != -1 && \"Invalid operand to eval(), not a value or "
                 "constant!\"");
    auto ret = new Cell();
    return *ret;
  } else if (vnumber < 0) {

    unsigned index = -vnumber - 2;
    return kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    StackFrame &sf = state.stack.back();
    return sf.locals[index];
  }
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state,
                         ref<Expr> value) {
  getDestCell(state, target).value = value;

  // yuhao: debug
  if (print) {
    if (isa<llvm::LoadInst>(target->inst)) {
      hy_log(0,
             "state: " + std::to_string(state.getID()) + " load bindLocal: ");
      std::string str;
      hy_dump(0, value->print, str);
    }
  }
}

void Executor::bindArgument(KFunction *kf, unsigned index,
                            ExecutionState &state, ref<Expr> value) {
  getArgumentCell(state, kf, index).value = value;
}

ref<Expr> Executor::toUnique(const ExecutionState &state, ref<Expr> &e) {
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    e = optimizer.optimizeExpr(e, true);
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state.constraints, e, value, state.queryMetaData)) {
      ref<Expr> cond = EqExpr::create(e, value);
      cond = optimizer.optimizeExpr(cond, false);
      if (solver->mustBeTrue(state.constraints, cond, isTrue,
                             state.queryMetaData) &&
          isTrue)
        result = value;
    }
    solver->setTimeout(time::Span());
  }

  return result;
}

/* Concretize the given expression, and return a possible constant value.
   'reason' is just a documentation string stating the reason for
   concretization. */
ref<klee::ConstantExpr> Executor::toConstant(ExecutionState &state, ref<Expr> e,
                                             const char *reason) {
  e = ConstraintManager::simplifyExpr(state.constraints, e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  // yuhao:
  ref<ConstantExpr> value = ConstantExpr::create(0, e->getWidth());
  solver->setTimeout(coreSolverTimeout);
  bool success =
      solver->getValue(state.constraints, e, value, state.queryMetaData);
  // assert(success && "FIXME: Unhandled solver failure");
  solver->setTimeout(time::Span());

  (void)success;

  std::string str;
  llvm::raw_string_ostream os(str);
  os << "silently concretizing (reason: " << reason << ") expression " << e
     << " to value " << value << " (" << (*(state.pc)).info->file << ":"
     << (*(state.pc)).info->line << ")";

  if (AllExternalWarnings)
    klee_warning("%s", os.str().c_str());
  else
    klee_warning_once(reason, "%s", os.str().c_str());

  addConstraint(state, EqExpr::create(e, value));

  return value;
}

void Executor::executeGetValue(ExecutionState &state, ref<Expr> e,
                               KInstruction *target) {
  e = ConstraintManager::simplifyExpr(state.constraints, e);
  std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
      seedMap.find(&state);
  if (it == seedMap.end() || isa<ConstantExpr>(e)) {

    // yuhao:
    ref<ConstantExpr> value = ConstantExpr::create(0, Expr::Bool);
    e = optimizer.optimizeExpr(e, true);
    // solver->setTimeout(coreSolverTimeout);
    bool success =
        solver->getValue(state.constraints, e, value, state.queryMetaData);
    // assert(success && "FIXME: Unhandled solver failure");
    // solver->setTimeout(time::Span());

    (void)success;
    bindLocal(target, state, value);
  } else {
    std::set<ref<Expr>> values;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
                                         siie = it->second.end();
         siit != siie; ++siit) {
      ref<Expr> cond = siit->assignment.evaluate(e);
      cond = optimizer.optimizeExpr(cond, true);

      // yuhao:
      ref<ConstantExpr> value = ConstantExpr::create(0, Expr::Bool);
      // solver->setTimeout(coreSolverTimeout);
      bool success =
          solver->getValue(state.constraints, cond, value, state.queryMetaData);
      // assert(success && "FIXME: Unhandled solver failure");
      // solver->setTimeout(time::Span());

      (void)success;
      values.insert(value);
    }

    std::vector<ref<Expr>> conditions;
    for (std::set<ref<Expr>>::iterator vit = values.begin(), vie = values.end();
         vit != vie; ++vit)
      conditions.push_back(EqExpr::create(e, *vit));

    std::vector<ExecutionState *> branches;
    branch(state, conditions, branches, BranchType::GetVal);

    std::vector<ExecutionState *>::iterator bit = branches.begin();
    for (std::set<ref<Expr>>::iterator vit = values.begin(), vie = values.end();
         vit != vie; ++vit) {
      ExecutionState *es = *bit;
      if (es)
        bindLocal(target, *es, *vit);
      ++bit;
    }
  }
}

void Executor::printDebugInstructions(ExecutionState &state) {
  // print nothing if option unset
  if (DebugPrintInstructions.getBits() == 0)
    return;

  // set output stream (stderr/file)
  llvm::raw_ostream *stream = nullptr;
  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(STDERR_SRC) ||
      DebugPrintInstructions.isSet(STDERR_COMPACT))
    stream = &llvm::errs();
  else
    stream = &debugLogBuffer;

  // print:
  //   [all]     src location:asm line:state ID:instruction
  //   [compact]              asm line:state ID
  //   [src]     src location:asm line:state ID
  if (!DebugPrintInstructions.isSet(STDERR_COMPACT) &&
      !DebugPrintInstructions.isSet(FILE_COMPACT)) {
    (*stream) << "     " << state.pc->getSourceLocation() << ':';
  }

  (*stream) << state.pc->info->assemblyLine << ':' << state.getID();

  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(FILE_ALL))
    (*stream) << ':' << *(state.pc->inst);

  (*stream) << '\n';

  // flush to file
  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    debugLogBuffer.flush();
    (*debugInstFile) << debugLogBuffer.str();
    debugBufferString = "";
  }
}

void Executor::stepInstruction(ExecutionState &state) {
  printDebugInstructions(state);
  if (statsTracker)
    statsTracker->stepInstruction(state);

  ++stats::instructions;
  ++state.steppedInstructions;
  state.prevPC = state.pc;
  ++state.pc;

  if (stats::instructions == MaxInstructions)
    haltExecution = true;
}

static inline const llvm::fltSemantics *fpWidthToSemantics(unsigned width) {
  switch (width) {
  case Expr::Int32:
    return &llvm::APFloat::IEEEsingle();
  case Expr::Int64:
    return &llvm::APFloat::IEEEdouble();
  case Expr::Fl80:
    return &llvm::APFloat::x87DoubleExtended();
  default:
    return 0;
  }
}

MemoryObject *Executor::serializeLandingpad(ExecutionState &state,
                                            const llvm::LandingPadInst &lpi,
                                            bool &stateTerminated) {
  stateTerminated = false;

  std::vector<unsigned char> serialized;

  for (unsigned current_clause_id = 0; current_clause_id < lpi.getNumClauses();
       ++current_clause_id) {
    llvm::Constant *current_clause = lpi.getClause(current_clause_id);
    if (lpi.isCatch(current_clause_id)) {
      // catch-clause
      serialized.push_back(0);

      std::uint64_t ti_addr = 0;

      llvm::BitCastOperator *clause_bitcast =
          dyn_cast<llvm::BitCastOperator>(current_clause);
      if (clause_bitcast) {
        llvm::GlobalValue *clause_type =
            dyn_cast<GlobalValue>(clause_bitcast->getOperand(0));

        ti_addr = globalAddresses[clause_type]->getZExtValue();
      } else if (current_clause->isNullValue()) {
        ti_addr = 0;
      } else {
        terminateStateOnExecError(
            state, "Internal: Clause is not a bitcast or null (catch-all)");
        stateTerminated = true;
        return nullptr;
      }
      const std::size_t old_size = serialized.size();
      serialized.resize(old_size + 8);
      memcpy(serialized.data() + old_size, &ti_addr, sizeof(ti_addr));
    } else if (lpi.isFilter(current_clause_id)) {
      if (current_clause->isNullValue()) {
        // special handling for a catch-all filter clause, i.e., "[0 x i8*]"
        // for this case we serialize 1 element..
        serialized.push_back(1);
        // which is a 64bit-wide 0.
        serialized.resize(serialized.size() + 8, 0);
      } else {
        llvm::ConstantArray const *ca =
            cast<llvm::ConstantArray>(current_clause);

        // serialize `num_elements+1` as unsigned char
        unsigned const num_elements = ca->getNumOperands();
        unsigned char serialized_num_elements = 0;

        if (num_elements >=
            std::numeric_limits<decltype(serialized_num_elements)>::max()) {
          terminateStateOnExecError(
              state, "Internal: too many elements in landingpad filter");
          stateTerminated = true;
          return nullptr;
        }

        serialized_num_elements = num_elements;
        serialized.push_back(serialized_num_elements + 1);

        // serialize the exception-types occurring in this filter-clause
        for (llvm::Value const *v : ca->operands()) {
          llvm::BitCastOperator const *bitcast =
              dyn_cast<llvm::BitCastOperator>(v);
          if (!bitcast) {
            terminateStateOnExecError(state,
                                      "Internal: expected value inside a "
                                      "filter-clause to be a bitcast");
            stateTerminated = true;
            return nullptr;
          }

          llvm::GlobalValue const *clause_value =
              dyn_cast<GlobalValue>(bitcast->getOperand(0));
          if (!clause_value) {
            terminateStateOnExecError(
                state, "Internal: expected value inside a "
                       "filter-clause bitcast to be a GlobalValue");
            stateTerminated = true;
            return nullptr;
          }

          std::uint64_t const ti_addr =
              globalAddresses[clause_value]->getZExtValue();

          const std::size_t old_size = serialized.size();
          serialized.resize(old_size + 8);
          memcpy(serialized.data() + old_size, &ti_addr, sizeof(ti_addr));
        }
      }
    }
  }

  MemoryObject *mo =
      memory->allocate(serialized.size(), true, false, &state, nullptr, 1);
  ObjectState *os = bindObjectInState(state, mo, false);
  for (unsigned i = 0; i < serialized.size(); i++) {
    os->write8(i, serialized[i]);
  }

  return mo;
}

void Executor::unwindToNextLandingpad(ExecutionState &state) {
  UnwindingInformation *ui = state.unwindingInformation.get();
  assert(ui && "unwinding without unwinding information");

  std::size_t startIndex;
  std::size_t lowestStackIndex;
  bool popFrames;

  if (auto *sui = dyn_cast<SearchPhaseUnwindingInformation>(ui)) {
    startIndex = sui->unwindingProgress;
    lowestStackIndex = 0;
    popFrames = false;
  } else if (auto *cui = dyn_cast<CleanupPhaseUnwindingInformation>(ui)) {
    startIndex = state.stack.size() - 1;
    lowestStackIndex = cui->catchingStackIndex;
    popFrames = true;
  } else {
    assert(false && "invalid UnwindingInformation subclass");
  }

  for (std::size_t i = startIndex; i > lowestStackIndex; i--) {
    auto const &sf = state.stack.at(i);

    Instruction *inst = sf.caller ? sf.caller->inst : nullptr;

    if (popFrames) {
      state.popFrame();
      if (statsTracker != nullptr) {
        statsTracker->framePopped(state);
      }
    }

    if (InvokeInst *invoke = dyn_cast<InvokeInst>(inst)) {
      // we found the next invoke instruction in the call stack, handle it
      // depending on the current phase.
      if (auto *sui = dyn_cast<SearchPhaseUnwindingInformation>(ui)) {
        // in the search phase, run personality function to check if this
        // landingpad catches the exception

        LandingPadInst *lpi = invoke->getUnwindDest()->getLandingPadInst();
        assert(lpi && "unwind target of an invoke instruction did not lead to "
                      "a landingpad");

        // check if this is a pure cleanup landingpad first
        if (lpi->isCleanup() && lpi->getNumClauses() == 0) {
          // pure cleanup lpi, this can't be a handler, so skip it
          continue;
        }

        bool stateTerminated = false;
        MemoryObject *clauses_mo =
            serializeLandingpad(state, *lpi, stateTerminated);
        assert((stateTerminated != bool(clauses_mo)) &&
               "illegal serializeLandingpad result");

        if (stateTerminated) {
          return;
        }

        assert(sui->serializedLandingpad == nullptr &&
               "serializedLandingpad should be reset");
        sui->serializedLandingpad = clauses_mo;

        llvm::Function *personality_fn =
            kmodule->module->getFunction("_klee_eh_cxx_personality");
        KFunction *kf = kmodule->functionMap[personality_fn];

        state.pushFrame(state.prevPC, kf);
        state.pc = kf->instructions;
        bindArgument(kf, 0, state, sui->exceptionObject);
        bindArgument(kf, 1, state, clauses_mo->getSizeExpr());
        bindArgument(kf, 2, state, clauses_mo->getBaseExpr());

        if (statsTracker) {
          statsTracker->framePushed(state,
                                    &state.stack[state.stack.size() - 2]);
        }

        // make sure we remember our search progress afterwards
        sui->unwindingProgress = i - 1;
      } else {
        // in the cleanup phase, redirect control flow
        transferToBasicBlock(invoke->getUnwindDest(), invoke->getParent(),
                             state);
      }

      // we are done, stop search/unwinding here
      return;
    }
  }

  // no further invoke instruction/landingpad found
  if (isa<SearchPhaseUnwindingInformation>(ui)) {
    // in phase 1, simply stop unwinding. this will return
    // control flow back to _Unwind_RaiseException, which will
    // return the correct error.

    // clean up unwinding state
    state.unwindingInformation.reset();
  } else {
    // in phase 2, this represent a situation that should
    // not happen, as we only progressed to phase 2 because
    // we found a handler in phase 1.
    // therefore terminate the state.
    terminateStateOnExecError(state,
                              "Missing landingpad in phase 2 of unwinding");
  }
}

ref<klee::ConstantExpr> Executor::getEhTypeidFor(ref<Expr> type_info) {
  // FIXME: Handling getEhTypeidFor is non-deterministic and depends on the
  //        order states have been processed and executed.
  auto eh_type_iterator =
      std::find(std::begin(eh_typeids), std::end(eh_typeids), type_info);
  if (eh_type_iterator == std::end(eh_typeids)) {
    eh_typeids.push_back(type_info);
    eh_type_iterator = std::prev(std::end(eh_typeids));
  }
  // +1 because typeids must always be positive, so they can be distinguished
  // from 'no landingpad clause matched' which has value 0
  auto res = ConstantExpr::create(eh_type_iterator - std::begin(eh_typeids) + 1,
                                  Expr::Int32);
  return res;
}

void Executor::executeCall(ExecutionState &state, KInstruction *ki, Function *f,
                           std::vector<ref<Expr>> &arguments) {
  Instruction *i = ki->inst;
  if (isa_and_nonnull<DbgInfoIntrinsic>(i))
    return;

  // yuhao: perform analysis for type info of user input
  type_analysis(state, ki, f, arguments);

  // yuhao: handle special functions early
  // check if specialFunctionHandler wants it
  if (const auto *func = dyn_cast<KFunction>(kmodule->functionMap[f])) {
    if (specialFunctionHandler->handle(state, func->function, ki, arguments))
      return;
  }

  if (f && f->isDeclaration()) {
    switch (f->getIntrinsicID()) {
    case Intrinsic::not_intrinsic: {
      // state may be destroyed by this call, cannot touch
      callExternalFunction(state, ki, kmodule->functionMap[f], arguments);
      break;
    }
    case Intrinsic::fabs: {
      ref<ConstantExpr> arg = toConstant(state, arguments[0], "floating point");
      if (!fpWidthToSemantics(arg->getWidth()))
        return terminateStateOnExecError(
            state, "Unsupported intrinsic llvm.fabs call");

      llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
                        arg->getAPValue());
      Res = llvm::abs(Res);

      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Intrinsic::fma:
    case Intrinsic::fmuladd: {
      // Both fma and fmuladd support float, double and fp80.  Note, that fp80
      // is not mentioned in the documentation of fmuladd, nevertheless, it is
      // still supported.  For details see
      // https://github.com/klee/klee/pull/1507/files#r894993332

      if (isa<VectorType>(i->getOperand(0)->getType()))
        return terminateStateOnExecError(
            state, f->getName() + " with vectors is not supported");

      ref<ConstantExpr> op1 =
          toConstant(state, eval(ki, 1, state).value, "floating point");
      ref<ConstantExpr> op2 =
          toConstant(state, eval(ki, 2, state).value, "floating point");
      ref<ConstantExpr> op3 =
          toConstant(state, eval(ki, 3, state).value, "floating point");

      if (!fpWidthToSemantics(op1->getWidth()) ||
          !fpWidthToSemantics(op2->getWidth()) ||
          !fpWidthToSemantics(op3->getWidth()))
        return terminateStateOnExecError(state, "Unsupported " + f->getName() +
                                                    " call");

      // (op1 * op2) + op3
      APFloat Res(*fpWidthToSemantics(op1->getWidth()), op1->getAPValue());
      Res.fusedMultiplyAdd(
          APFloat(*fpWidthToSemantics(op2->getWidth()), op2->getAPValue()),
          APFloat(*fpWidthToSemantics(op3->getWidth()), op3->getAPValue()),
          APFloat::rmNearestTiesToEven);

      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

#if LLVM_VERSION_CODE >= LLVM_VERSION(12, 0)
    case Intrinsic::abs: {
      if (isa<VectorType>(i->getOperand(0)->getType()))
        return terminateStateOnExecError(
            state, "llvm.abs with vectors is not supported");

      ref<Expr> op = eval(ki, 1, state).value;
      ref<Expr> poison = eval(ki, 2, state).value;

      assert(poison->getWidth() == 1 && "Second argument is not an i1");
      unsigned bw = op->getWidth();

      uint64_t moneVal = APInt(bw, -1, true).getZExtValue();
      uint64_t sminVal = APInt::getSignedMinValue(bw).getZExtValue();

      ref<ConstantExpr> zero = ConstantExpr::create(0, bw);
      ref<ConstantExpr> mone = ConstantExpr::create(moneVal, bw);
      ref<ConstantExpr> smin = ConstantExpr::create(sminVal, bw);

      if (poison->isTrue()) {
        ref<Expr> issmin = EqExpr::create(op, smin);
        if (issmin->isTrue())
          return terminateStateOnExecError(
              state, "llvm.abs called with poison and INT_MIN");
      }

      // conditions to flip the sign: INT_MIN < op < 0
      ref<Expr> negative = SltExpr::create(op, zero);
      ref<Expr> notsmin = NeExpr::create(op, smin);
      ref<Expr> cond = AndExpr::create(negative, notsmin);

      // flip and select the result
      ref<Expr> flip = MulExpr::create(op, mone);
      ref<Expr> result = SelectExpr::create(cond, flip, op);

      bindLocal(ki, state, result);
      break;
    }

    case Intrinsic::smax:
    case Intrinsic::smin:
    case Intrinsic::umax:
    case Intrinsic::umin: {
      if (isa<VectorType>(i->getOperand(0)->getType()) ||
          isa<VectorType>(i->getOperand(1)->getType()))
        return terminateStateOnExecError(
            state, "llvm.{s,u}{max,min} with vectors is not supported");

      ref<Expr> op1 = eval(ki, 1, state).value;
      ref<Expr> op2 = eval(ki, 2, state).value;

      ref<Expr> cond = nullptr;
      if (f->getIntrinsicID() == Intrinsic::smax)
        cond = SgtExpr::create(op1, op2);
      else if (f->getIntrinsicID() == Intrinsic::smin)
        cond = SltExpr::create(op1, op2);
      else if (f->getIntrinsicID() == Intrinsic::umax)
        cond = UgtExpr::create(op1, op2);
      else // (f->getIntrinsicID() == Intrinsic::umin)
        cond = UltExpr::create(op1, op2);

      ref<Expr> result = SelectExpr::create(cond, op1, op2);
      bindLocal(ki, state, result);
      break;
    }
#endif

    case Intrinsic::fshr:
    case Intrinsic::fshl: {
      ref<Expr> op1 = eval(ki, 1, state).value;
      ref<Expr> op2 = eval(ki, 2, state).value;
      ref<Expr> op3 = eval(ki, 3, state).value;
      unsigned w = op1->getWidth();
      assert(w == op2->getWidth() && "type mismatch");
      assert(w == op3->getWidth() && "type mismatch");
      ref<Expr> c = ConcatExpr::create(op1, op2);
      // op3 = zeroExtend(op3 % w)
      op3 = URemExpr::create(op3, ConstantExpr::create(w, w));
      op3 = ZExtExpr::create(op3, w + w);
      if (f->getIntrinsicID() == Intrinsic::fshl) {
        // shift left and take top half
        ref<Expr> s = ShlExpr::create(c, op3);
        bindLocal(ki, state, ExtractExpr::create(s, w, w));
      } else {
        // shift right and take bottom half
        // note that LShr and AShr will have same behaviour
        ref<Expr> s = LShrExpr::create(c, op3);
        bindLocal(ki, state, ExtractExpr::create(s, 0, w));
      }
      break;
    }

    // va_arg is handled by caller and intrinsic lowering, see comment for
    // ExecutionState::varargs
    case Intrinsic::vastart: {
      StackFrame &sf = state.stack.back();

      // varargs can be zero if no varargs were provided
      if (!sf.varargs)
        return;

      // FIXME: This is really specific to the architecture, not the pointer
      // size. This happens to work for x86-32 and x86-64, however.
      Expr::Width WordSize = Context::get().getPointerWidth();
      if (WordSize == Expr::Int32) {
        executeMemoryOperation(state, true, arguments[0],
                               sf.varargs->getBaseExpr(), 0, 1);
      } else {
        assert(WordSize == Expr::Int64 && "Unknown word size!");

        // x86-64 has quite complicated calling convention. However,
        // instead of implementing it, we can do a simple hack: just
        // make a function believe that all varargs are on stack.
        executeMemoryOperation(state, true, arguments[0],
                               ConstantExpr::create(48, 32), 0, 1); // gp_offset
        executeMemoryOperation(
            state, true,
            AddExpr::create(arguments[0], ConstantExpr::create(4, 64)),
            ConstantExpr::create(304, 32), 0, 1); // fp_offset
        executeMemoryOperation(
            state, true,
            AddExpr::create(arguments[0], ConstantExpr::create(8, 64)),
            sf.varargs->getBaseExpr(), 0, 1); // overflow_arg_area
        executeMemoryOperation(
            state, true,
            AddExpr::create(arguments[0], ConstantExpr::create(16, 64)),
            ConstantExpr::create(0, 64), 0, 1); // reg_save_area
      }
      break;
    }

#ifdef SUPPORT_KLEE_EH_CXX
    case Intrinsic::eh_typeid_for: {
      bindLocal(ki, state, getEhTypeidFor(arguments.at(0)));
      break;
    }
#endif

    case Intrinsic::vaend:
      // va_end is a noop for the interpreter.
      //
      // FIXME: We should validate that the target didn't do something bad
      // with va_end, however (like call it twice).
      break;

    case Intrinsic::vacopy:
      // va_copy should have been lowered.
      //
      // FIXME: It would be nice to check for errors in the usage of this as
      // well.
    default:
      klee_warning("unimplemented intrinsic: %s", f->getName().data());
      terminateStateOnExecError(state, "unimplemented intrinsic");
      return;
    }

    if (InvokeInst *ii = dyn_cast<InvokeInst>(i)) {
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
    }
  } else {
    // Check if maximum stack size was reached.
    // We currently only count the number of stack frames
    if (RuntimeMaxStackFrames && state.stack.size() > RuntimeMaxStackFrames) {
      terminateStateEarly(state, "Maximum stack size reached.",
                          StateTerminationType::OutOfStackMemory);
      klee_warning("Maximum stack size reached.");
      return;
    }

    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = kmodule->functionMap[f];

    state.pushFrame(state.prevPC, kf);
    state.pc = kf->instructions;

    if (statsTracker)
      statsTracker->framePushed(state, &state.stack[state.stack.size() - 2]);

    // TODO: support zeroext, signext, sret attributes

    unsigned callingArgs = arguments.size();
    unsigned funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs) {
        klee_warning_once(f, "calling %s with extra arguments.",
                          f->getName().data());
      } else if (callingArgs < funcArgs) {
        terminateStateOnUserError(state,
                                  "calling function with too few arguments");
        return;
      }
    } else {
      if (callingArgs < funcArgs) {
        terminateStateOnUserError(state,
                                  "calling function with too few arguments");
        return;
      }

      // Only x86-32 and x86-64 are supported
      Expr::Width WordSize = Context::get().getPointerWidth();
      assert(((WordSize == Expr::Int32) || (WordSize == Expr::Int64)) &&
             "Unknown word size!");

      uint64_t size = 0; // total size of variadic arguments
      bool requires16ByteAlignment = false;

      uint64_t offsets[callingArgs]; // offsets of variadic arguments
      uint64_t argWidth;             // width of current variadic argument

      const CallBase &cb = cast<CallBase>(*i);
      for (unsigned k = funcArgs; k < callingArgs; k++) {
        if (cb.isByValArgument(k)) {
          Type *t = cb.getParamByValType(k);
          argWidth = kmodule->targetData->getTypeSizeInBits(t);
        } else {
          argWidth = arguments[k]->getWidth();
        }

#if LLVM_VERSION_CODE >= LLVM_VERSION(11, 0)
        MaybeAlign ma = cb.getParamAlign(k);
        unsigned alignment = ma ? ma->value() : 0;
#else
        unsigned alignment = cb.getParamAlignment(k);
#endif

        if (WordSize == Expr::Int32 && !alignment)
          alignment = 4;
        else {
          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a
          // 16 byte boundary if alignment needed by type exceeds 8 byte
          // boundary.
          if (!alignment && argWidth > Expr::Int64) {
            alignment = 16;
            requires16ByteAlignment = true;
          }

          if (!alignment)
            alignment = 8;
        }

        size = llvm::alignTo(size, alignment);
        offsets[k] = size;

        if (WordSize == Expr::Int32)
          size += Expr::getMinBytesForWidth(argWidth);
        else {
          // AMD64-ABI 3.5.7p5: Step 9. Set l->overflow_arg_area to:
          // l->overflow_arg_area + sizeof(type)
          // Step 10. Align l->overflow_arg_area upwards to an 8 byte boundary.
          size += llvm::alignTo(argWidth, WordSize) / 8;
        }
      }

      StackFrame &sf = state.stack.back();
      MemoryObject *mo = sf.varargs =
          memory->allocate(size, true, false, &state, state.prevPC->inst,
                           (requires16ByteAlignment ? 16 : 8));
      if (!mo && size) {
        terminateStateOnExecError(state, "out of memory (varargs)");
        return;
      }

      if (mo) {
        if ((WordSize == Expr::Int64) && (mo->address & 15) &&
            requires16ByteAlignment) {
          // Both 64bit Linux/Glibc and 64bit MacOSX should align to 16 bytes.
          klee_warning_once(
              0, "While allocating varargs: malloc did not align to 16 bytes.");
        }

        ObjectState *os = bindObjectInState(state, mo, true);

        for (unsigned k = funcArgs; k < callingArgs; k++) {
          if (!cb.isByValArgument(k)) {
            os->write(offsets[k], arguments[k]);
          } else {
            ConstantExpr *CE = dyn_cast<ConstantExpr>(arguments[k]);
            assert(CE); // byval argument needs to be a concrete pointer

            ObjectPair op;
            state.addressSpace.resolveOne(CE, op);
            const ObjectState *osarg = op.second;
            assert(osarg);
            for (unsigned i = 0; i < osarg->size; i++)
              os->write(offsets[k] + i, osarg->read8(i));
          }
        }
      }
    }

    unsigned numFormals = f->arg_size();
    for (unsigned k = 0; k < numFormals; k++)
      bindArgument(kf, k, state, arguments[k]);
  }
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src,
                                    ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the eval() result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.

  // XXX this lookup has to go ?
  KFunction *kf = state.stack.back().kf;
  unsigned entry = kf->basicBlockEntry[dst];
  state.pc = &kf->instructions[entry];
  if (state.pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode *>(state.pc->inst);
    state.incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

/// Compute the true target of a function call, resolving LLVM aliases
/// and bitcasts.
Function *Executor::getTargetFunction(Value *calledVal) {
  SmallPtrSet<const GlobalValue *, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv).second)
        return 0;

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode() == Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

void Executor::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;

  // yuhao: debug
  std::string str;
  if (i->getParent()->getParent()->getName() == "midisynth_unuse") {
    print = false;
  } else {
    print = false;
  }
  if (print) {
    hy_log(0,
           "state id: " + std::to_string(state.getID()) + " " + dump_inst(i));
    hy_dump(0, i->print, str);
  }

  switch (i->getOpcode()) {
    // Control flow
  case Instruction::Ret: {
    ReturnInst *ri = cast<ReturnInst>(i);
    KInstIterator kcaller = state.stack.back().caller;
    Instruction *caller = kcaller ? kcaller->inst : nullptr;
    bool isVoidReturn = (ri->getNumOperands() == 0);
    ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);

    if (!isVoidReturn) {
      result = eval(ki, 0, state).value;
    }

    if (state.stack.size() <= 1) {
      assert(!caller && "caller set on initial stack frame");

      // yuhao: save all the finished states when the main function returns
      states_after_running.push_back(new ExecutionState(state));

      terminateStateOnExit(state);
    } else {
      state.popFrame();

      if (statsTracker)
        statsTracker->framePopped(state);

      if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
        transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
      } else {
        state.pc = kcaller;
        ++state.pc;
      }

#ifdef SUPPORT_KLEE_EH_CXX
      if (ri->getFunction()->getName() == "_klee_eh_cxx_personality") {
        assert(dyn_cast<ConstantExpr>(result) &&
               "result from personality fn must be a concrete value");

        auto *sui = dyn_cast_or_null<SearchPhaseUnwindingInformation>(
            state.unwindingInformation.get());
        assert(sui && "return from personality function outside of "
                      "search phase unwinding");

        // unbind the MO we used to pass the serialized landingpad
        state.addressSpace.unbindObject(sui->serializedLandingpad);
        sui->serializedLandingpad = nullptr;

        if (result->isZero()) {
          // this lpi doesn't handle the exception, continue the search
          unwindToNextLandingpad(state);
        } else {
          // a clause (or a catch-all clause or filter clause) matches:
          // remember the stack index and switch to cleanup phase
          state.unwindingInformation =
              std::make_unique<CleanupPhaseUnwindingInformation>(
                  sui->exceptionObject, cast<ConstantExpr>(result),
                  sui->unwindingProgress);
          // this pointer is now invalidated
          sui = nullptr;
          // continue the unwinding process (which will now start with the
          // cleanup phase)
          unwindToNextLandingpad(state);
        }

        // never return normally from the personality fn
        break;
      }
#endif // SUPPORT_KLEE_EH_CXX

      if (!isVoidReturn) {
        Type *t = caller->getType();
        if (t != Type::getVoidTy(i->getContext())) {
          // may need to do coercion due to bitcasts
          Expr::Width from = result->getWidth();
          Expr::Width to = getWidthForLLVMType(t);

          if (from != to) {
            const CallBase &cb = cast<CallBase>(*caller);

            // XXX need to check other param attrs ?
            bool isSExt = cb.hasRetAttr(llvm::Attribute::SExt);
            if (isSExt) {
              result = SExtExpr::create(result, to);
            } else {
              result = ZExtExpr::create(result, to);
            }
          }

          bindLocal(kcaller, state, result);
        }
      } else {
        // We check that the return value has no users instead of
        // checking the type, since C defaults to returning int for
        // undeclared functions.
        if (!caller->use_empty()) {
          terminateStateOnExecError(
              state, "return void when caller expected a result");
        }
      }
    }
    break;
  }
  // yuhao:
  case Instruction::CallBr: {
    CallBrInst *bi = cast<CallBrInst>(i);
    ref<Expr> cond = manual_make_symbolic(
        state, get_symbolic_name(asm_return_name, asm_return_count), i, 1, 1);

    Executor::StatePair branches =
        fork(state, cond, false, BranchType::Conditional);

    // NOTE: There is a hidden dependency here, markBranchVisited
    // requires that we still be in the context of the branch
    // instruction (it reuses its statistic id). Should be cleaned
    // up with convenient instruction specific data.
    if (statsTracker && state.stack.back().kf->trackCoverage)
      statsTracker->markBranchVisited(branches.first, branches.second);

    if (branches.first)
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(),
                           *branches.first);
    if (branches.second)
      transferToBasicBlock(bi->getSuccessor(1), bi->getParent(),
                           *branches.second);

    // yuhao: specification gudied fork
    specification_guided_fork(branches, bi);

    break;
  }
  case Instruction::Br: {
    BranchInst *bi = cast<BranchInst>(i);
    if (bi->isUnconditional()) {
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
    } else {
      // FIXME: Find a way that we don't have this hidden dependency.
      assert(bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
      ref<Expr> cond = eval(ki, 0, state).value;

      // yuhao: debug
      int debug = -1;
      str = "br cond: ";
      hy_add_dump(debug, cond->print, str);
      for (auto c : state.constraints) {
        str = "br constraints: ";
        hy_add_dump(debug, c->print, str);
      }
      for (auto ucmo : state.under_constrained_memory_objects) {
        if (ucmo.second->is_created) {
          str = "br ucmo constraints1: ";
          hy_add_dump(debug, ucmo.second->base_address->print, str);
          str = "br ucmo constraints2: ";
          hy_add_dump(debug, ucmo.second->real_address->print, str);
        }
      }
      for (auto c : *state.ucmo_constraints) {
        str = "br smo constraints: ";
        hy_add_dump(debug, c->print, str);
      }

      cond = optimizer.optimizeExpr(cond, false);
      Executor::StatePair branches =
          fork(state, cond, false, BranchType::Conditional);

      // yuhao:
      str = "br cond after: ";
      hy_add_dump(debug, cond->print, str);

      // NOTE: There is a hidden dependency here, markBranchVisited
      // requires that we still be in the context of the branch
      // instruction (it reuses its statistic id). Should be cleaned
      // up with convenient instruction specific data.
      if (statsTracker && state.stack.back().kf->trackCoverage)
        statsTracker->markBranchVisited(branches.first, branches.second);

      if (branches.first) {
        // yuhao: debug
        hy_log(debug,
               "br ssuccessor 0: " + bi->getSuccessor(0)->getName().str());

        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(),
                             *branches.first);
      }
      if (branches.second) {
        // yuhao: debug
        hy_log(debug,
               "br ssuccessor 1: " + bi->getSuccessor(1)->getName().str());

        transferToBasicBlock(bi->getSuccessor(1), bi->getParent(),
                             *branches.second);
      }

      // yuhao: specification gudied fork
      specification_guided_fork(branches, bi);

      std::string func_name = bi->getFunction()->getName().str();
      if (func_name.find("memcpy") != std::string::npos) {
        if (branches.first == nullptr && branches.second) {
          break;
        } else if (branches.first && branches.second) {
          terminateStateEarly(*branches.second,
                              "symbolic loop unrolling in memcpy: ",
                              StateTerminationType::MaxDepth);

          hy_log(-1, "terminateStateEarly state: " +
                         std::to_string(branches.second->getID()));
          break;
        } else {
          break;
        }
      }

      // yuhao: not fork for symbolic loop unrolling > n -1 times
      // yuhao: compute the number of times to fork
      std::string str;
      uint64_t n = 2;
      if (branches.first && branches.second) {
        // symbolic condition and fork
        std::set<std::string> names;
        resolve_symbolic_expr(cond, names);
        if (is_all_related(names, input_name)) {
          // all related to input
          n = 256;
        } else if (is_related(names, input_name)) {
          // some related to input
          n = 4;
        } else {
          // not related to input
          n = 2;
        }
      } else if (!isa<ConstantExpr>(cond)) {
        // symbolic condition but no fork
        n = 3;
        // std::set<std::string> names;
        // resolve_symbolic_expr(cond, names);
        // if (is_all_related(names, input_name)) {
        //   // all related to input
        //   n = 3;
        // } else if (is_related(names, input_name)) {
        //   // some related to input
        //   n = 3;
        // } else {
        //   // not related to input
        //   n = 3;
        // }
      } else {
        // no symbolic condition and no fork
        n = 1024;
      }

      // yuhao: only fork n - 1 times
      if (branches.first) {
        StackFrame &sf = branches.first->stack.back();
        if (sf.loop_map.find(i->getParent()) == sf.loop_map.end()) {
          sf.loop_map[i->getParent()] = 1;
        } else {
          sf.loop_map[i->getParent()]++;
        }
        hy_dump(-1, branches.first->dumpStack, str);
        for (auto lm : branches.first->stack.back().loop_map) {
          hy_log(-1, "1 loop_map: " + lm.first->getName().str() + ": " +
                         std::to_string(lm.second));
        }

        if (sf.loop_map[i->getParent()] > n) {
          terminateStateEarly(*branches.first,
                              "symbolic loop 1 unrolling max: " +
                                  std::to_string(n),
                              StateTerminationType::MaxDepth);

          hy_log(-1, "terminateStateEarly state: " +
                         std::to_string(branches.first->getID()));
        }
      }
      if (branches.second) {
        StackFrame &sf = branches.second->stack.back();
        if (sf.loop_map.find(i->getParent()) == sf.loop_map.end()) {
          sf.loop_map[i->getParent()] = 1;
        } else {
          sf.loop_map[i->getParent()]++;
        }
        hy_dump(-1, branches.second->dumpStack, str);
        for (auto lm : branches.second->stack.back().loop_map) {
          hy_log(-1, "2 loop_map: " + lm.first->getName().str() + ": " +
                         std::to_string(lm.second));
        }

        if (sf.loop_map[i->getParent()] > n) {
          terminateStateEarly(*branches.second,
                              "symbolic loop 2 unrolling max: " +
                                  std::to_string(n),
                              StateTerminationType::MaxDepth);

          hy_log(-1, "terminateStateEarly state: " +
                         std::to_string(branches.second->getID()));
        }
      }
    }
    break;
  }
  case Instruction::IndirectBr: {
    // implements indirect branch to a label within the current function
    const auto bi = cast<IndirectBrInst>(i);
    auto address = eval(ki, 0, state).value;
    address = toUnique(state, address);

    // concrete address
    if (const auto CE = dyn_cast<ConstantExpr>(address.get())) {
      const auto bb_address =
          (BasicBlock *)CE->getZExtValue(Context::get().getPointerWidth());
      transferToBasicBlock(bb_address, bi->getParent(), state);
      break;
    }

    // symbolic address
    const auto numDestinations = bi->getNumDestinations();
    std::vector<BasicBlock *> targets;
    targets.reserve(numDestinations);
    std::vector<ref<Expr>> expressions;
    expressions.reserve(numDestinations);

    ref<Expr> errorCase = ConstantExpr::alloc(1, Expr::Bool);
    SmallPtrSet<BasicBlock *, 5> destinations;
    // collect and check destinations from label list
    for (unsigned k = 0; k < numDestinations; ++k) {
      // filter duplicates
      const auto d = bi->getDestination(k);
      if (destinations.count(d))
        continue;
      destinations.insert(d);

      // create address expression
      const auto PE = Expr::createPointer(reinterpret_cast<std::uint64_t>(d));
      ref<Expr> e = EqExpr::create(address, PE);

      // exclude address from errorCase
      errorCase = AndExpr::create(errorCase, Expr::createIsZero(e));

      // check feasibility
      bool result;
      solver->setTimeout(coreSolverTimeout);
      bool success __attribute__((unused)) =
          solver->mayBeTrue(state.constraints, e, result, state.queryMetaData);
      solver->setTimeout(time::Span());
      // assert(success && "FIXME: Unhandled solver failure");
      if (!success) {
        result = true;
      }
      if (result) {
        targets.push_back(d);
        expressions.push_back(e);
      }
    }
    // check errorCase feasibility
    bool result;
    solver->setTimeout(coreSolverTimeout);
    bool success __attribute__((unused)) = solver->mayBeTrue(
        state.constraints, errorCase, result, state.queryMetaData);
    solver->setTimeout(time::Span());
    // assert(success && "FIXME: Unhandled solver failure");
    if (!success) {
      result = true;
    }
    if (result) {
      expressions.push_back(errorCase);
    }

    // fork states
    std::vector<ExecutionState *> branches;
    branch(state, expressions, branches, BranchType::Indirect);

    // terminate error state
    if (result) {
      terminateStateOnExecError(*branches.back(),
                                "indirectbr: illegal label address");
      branches.pop_back();
    }

    // branch states to resp. target blocks
    assert(targets.size() == branches.size());
    for (std::vector<ExecutionState *>::size_type k = 0; k < branches.size();
         ++k) {
      if (branches[k]) {
        transferToBasicBlock(targets[k], bi->getParent(), *branches[k]);
      }
    }

    break;
  }
  case Instruction::Switch: {
    SwitchInst *si = cast<SwitchInst>(i);
    ref<Expr> cond = eval(ki, 0, state).value;
    BasicBlock *bb = si->getParent();

    cond = toUnique(state, cond);
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
      // Somewhat gross to create these all the time, but fine till we
      // switch to an internal rep.
      llvm::IntegerType *Ty = cast<IntegerType>(si->getCondition()->getType());
      ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
      unsigned index = si->findCaseValue(ci)->getSuccessorIndex();
      transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
    } else {
      // Handle possible different branch targets

      // We have the following assumptions:
      // - each case value is mutual exclusive to all other values
      // - order of case branches is based on the order of the expressions of
      //   the case values, still default is handled last
      std::vector<BasicBlock *> bbOrder;
      std::map<BasicBlock *, ref<Expr>> branchTargets;

      std::map<ref<Expr>, BasicBlock *> expressionOrder;

      // Iterate through all non-default cases and order them by expressions
      for (auto i : si->cases()) {
        ref<Expr> value = evalConstant(i.getCaseValue());

        BasicBlock *caseSuccessor = i.getCaseSuccessor();
        expressionOrder.insert(std::make_pair(value, caseSuccessor));
      }

      // Track default branch values
      ref<Expr> defaultValue = ConstantExpr::alloc(1, Expr::Bool);

      // iterate through all non-default cases but in order of the expressions
      for (std::map<ref<Expr>, BasicBlock *>::iterator
               it = expressionOrder.begin(),
               itE = expressionOrder.end();
           it != itE; ++it) {
        ref<Expr> match = EqExpr::create(cond, it->first);

        // skip if case has same successor basic block as default case
        // (should work even with phi nodes as a switch is a single terminating
        // instruction)
        if (it->second == si->getDefaultDest())
          continue;

        // Make sure that the default value does not contain this target's value
        defaultValue = AndExpr::create(defaultValue, Expr::createIsZero(match));

        // Check if control flow could take this case
        bool result;
        match = optimizer.optimizeExpr(match, false);
        solver->setTimeout(coreSolverTimeout);
        bool success = solver->mayBeTrue(state.constraints, match, result,
                                         state.queryMetaData);
        solver->setTimeout(time::Span());
        // assert(success && "FIXME: Unhandled solver failure");
        if (!success) {
          result = true;
        }
        (void)success;
        if (result) {
          BasicBlock *caseSuccessor = it->second;

          // Handle the case that a basic block might be the target of multiple
          // switch cases.
          // Currently we generate an expression containing all switch-case
          // values for the same target basic block. We spare us forking too
          // many times but we generate more complex condition expressions
          // TODO Add option to allow to choose between those behaviors
          std::pair<std::map<BasicBlock *, ref<Expr>>::iterator, bool> res =
              branchTargets.insert(std::make_pair(
                  caseSuccessor, ConstantExpr::alloc(0, Expr::Bool)));

          res.first->second = OrExpr::create(match, res.first->second);

          // Only add basic blocks which have not been target of a branch yet
          if (res.second) {
            bbOrder.push_back(caseSuccessor);
          }
        }
      }

      // Check if control could take the default case
      defaultValue = optimizer.optimizeExpr(defaultValue, false);
      bool res;
      solver->setTimeout(coreSolverTimeout);
      bool success = solver->mayBeTrue(state.constraints, defaultValue, res,
                                       state.queryMetaData);
      solver->setTimeout(time::Span());
      // assert(success && "FIXME: Unhandled solver failure");
      if (!success) {
        res = true;
      }
      (void)success;
      if (res) {
        std::pair<std::map<BasicBlock *, ref<Expr>>::iterator, bool> ret =
            branchTargets.insert(
                std::make_pair(si->getDefaultDest(), defaultValue));
        if (ret.second) {
          bbOrder.push_back(si->getDefaultDest());
        }
      }

      // Fork the current state with each state having one of the possible
      // successors of this switch
      std::vector<ref<Expr>> conditions;
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        conditions.push_back(branchTargets[*it]);
      }
      std::vector<ExecutionState *> branches;
      branch(state, conditions, branches, BranchType::Switch);

      std::vector<ExecutionState *>::iterator bit = branches.begin();
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        ExecutionState *es = *bit;
        if (es)
          transferToBasicBlock(*it, bb, *es);
        ++bit;
      }
    }
    break;
  }
  case Instruction::Unreachable:
    // Note that this is not necessarily an internal bug, llvm will
    // generate unreachable instructions in cases where it knows the
    // program will crash. So it is effectively a SEGV or internal
    // error.
    terminateStateOnExecError(state, "reached \"unreachable\" instruction");
    break;

  case Instruction::Invoke:
  case Instruction::Call: {
    // Ignore debug intrinsic calls
    if (isa<DbgInfoIntrinsic>(i))
      break;

    const CallBase &cb = cast<CallBase>(*i);
    Value *fp = cb.getCalledOperand();
    unsigned numArgs = cb.arg_size();
    Function *f = getTargetFunction(fp);

    // evaluate arguments
    std::vector<ref<Expr>> arguments;
    arguments.reserve(numArgs);

    for (unsigned j = 0; j < numArgs; ++j) {
      // yuhao:
      if (ki->operands[j + 1] == -1) {
      } else {
        arguments.push_back(eval(ki, j + 1, state).value);
      }
    }

    // yuhao: debug
    int64_t debug = -1;
    if (print) {
      hy_dump(debug, i->print, str);
      for (const auto &temp : arguments) {
        hy_dump(debug, temp->print, str);
      }
    }

    if (auto *asmValue =
            dyn_cast<InlineAsm>(fp)) { // TODO: move to `executeCall`
      if (ExternalCalls != ExternalCallPolicy::None) {
        KInlineAsm callable(asmValue);
        callExternalFunction(state, ki, &callable, arguments);
      } else {
        // yuhao:
        // terminateStateOnExecError(state, "external calls disallowed (in
        // particular inline asm)");
        llvm::Type *returnType = cb.getType();

        hy_log(debug, asmValue->getAsmString());

        if (asmValue->getAsmString().find("call __get_user_$") !=
            std::string::npos) {
          // yuhao: read value from address argument 0, and store the value to
          // the field 1 of return value
          int64_t debug_get_user = -1;
          hy_log(debug_get_user, "call __get_user_$");

          // yuhao: read value from arguemnt 0
          hy_log(debug_get_user,
                 "call __get_user_$: read value from arguemnt 0");
          llvm::StructType *st = llvm::cast<llvm::StructType>(returnType);
          llvm::Type *field_type = st->getElementType(1);
          Expr::Width field_type_size = getWidthForLLVMType(field_type);
          executeMemoryOperation(state, false, arguments[0], 0, ki, 0,
                                 field_type_size);
          ref<Expr> field_value = getDestCell(state, ki).value;
          hy_dump(debug_get_user, field_value->print, str);

          // yuhao: create symbolic return value
          hy_log(debug_get_user,
                 "call __get_user_$: create symbolic return value");
          auto symbolic_name =
              get_symbolic_name(asm_return_name, asm_return_count);
          unsigned int type_store_size =
              kmodule->targetData->getTypeStoreSize(returnType);
          Expr::Width type_size = getWidthForLLVMType(returnType);
          MemoryObject *mo =
              create_ucmo(state, symbolic_name, i, type_store_size, returnType);

          const ObjectState *os = state.addressSpace.findObject(mo);
          ref<Expr> old_asm_return = os->read(0, type_size);
          hy_dump(debug_get_user, old_asm_return->print, str);

          // yuhao: write value from user to return value
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          const StructLayout *sl = kmodule->targetData->getStructLayout(st);
          uint64_t offset_0 = sl->getElementOffset(0);
          wos->write(offset_0,
                     ConstantExpr::create(
                         0, getWidthForLLVMType(st->getElementType(0))));
          uint64_t offset_1 = sl->getElementOffset(1);
          wos->write(offset_1, field_value);

          ref<Expr> asm_return = os->read(0, type_size);
          bindLocal(ki, state, asm_return);
          hy_dump(debug_get_user, asm_return->print, str);
        } else if (asmValue->getAsmString().find("call __put_user_$") !=
                   std::string::npos) {

          // yuhao: write value of argument 1 to address argument 0
          int64_t debug_put_user = -1;
          hy_log(debug_put_user, "call __put_user_$");

          // yuhao: for the write
          Expr::Width field_type_size =
              getWidthForLLVMType(cb.getOperand(1)->getType());
          executeMemoryOperation(state, true, arguments[0], arguments[1], ki, 0,
                                 field_type_size);

          Expr::Width type_size = getWidthForLLVMType(returnType);
          ref<Expr> asm_return = ConstantExpr::create(0, type_size);
          bindLocal(ki, state, asm_return);
          hy_dump(debug_put_user, asm_return->print, str);
        } else if (!returnType->isVoidTy()) {
          auto symbolic_name =
              get_symbolic_name(asm_return_name, asm_return_count);
          unsigned int type_store_size =
              kmodule->targetData->getTypeStoreSize(returnType);
          Expr::Width type_size = getWidthForLLVMType(returnType);
          ref<Expr> asm_return = Executor::manual_make_symbolic(
              state, symbolic_name, i, type_store_size, type_size, returnType);
          bindLocal(ki, state, asm_return);

          str = "";
          str += "make asm return: " + symbolic_name + "\n";
          hy_add(debug, i->print, str);
          str += "\n";
          hy_add(debug, state.dumpStack, str);
          hy_log(debug, str);
          hy_dump(debug, asm_return->print, str);
        }
      }
      break;
    }

    if (f) {
      const FunctionType *fType = f->getFunctionType();
      const FunctionType *fpType =
          dyn_cast<FunctionType>(fp->getType()->getPointerElementType());

      // special case the call with a bitcast case
      if (fType != fpType) {
        assert(fType && fpType && "unable to get function type");

        // XXX check result coercion

        // XXX this really needs thought and validation
        unsigned i = 0;
        for (std::vector<ref<Expr>>::iterator ai = arguments.begin(),
                                              ie = arguments.end();
             ai != ie; ++ai) {
          Expr::Width to, from = (*ai)->getWidth();

          if (i < fType->getNumParams()) {
            to = getWidthForLLVMType(fType->getParamType(i));

            if (from != to) {
              // XXX need to check other param attrs ?
              bool isSExt = cb.paramHasAttr(i, llvm::Attribute::SExt);
              if (isSExt) {
                arguments[i] = SExtExpr::create(arguments[i], to);
              } else {
                arguments[i] = ZExtExpr::create(arguments[i], to);
              }
            }
          }

          i++;
        }
      }

      executeCall(state, ki, f, arguments);
    } else {
      ref<Expr> v = eval(ki, 0, state).value;

      ExecutionState *free = &state;
      // bool hasInvalid = false, first = true;
      bool first = true;

      /* XXX This is wasteful, no need to do a full evaluate since we
         have already got a value. But in the end the caches should
         handle it for us, albeit with some overhead. */

      // yuhao: handle function pointer

      v = toUnique_ucmo(state, v);
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(v.get())) {
        uint64_t addr = CE->getZExtValue();
        if (legalFunctions.find(addr) != legalFunctions.end()) {
          f = legalFunctions[addr];
          executeCall(state, ki, f, arguments);
          break;
        }
      }

      // yuhao: handle function pointer
      hy_log(debug, "indirect call: " + dump_inst(i));

      llvm::CallInst *ci = llvm::cast<llvm::CallInst>(i);
      if (GlobalCtx.Callees.find(ci) == GlobalCtx.Callees.end()) {
      } else {
        for (auto temp_f : GlobalCtx.Callees[ci]) {
          f = temp_f;
          hy_log(debug, "find callee: " + f->getName().str());
          if (legalFunctionsAddress.find(f) == legalFunctionsAddress.end()) {
            continue;
          }

          // yuhao: stop recursive call
          bool is_recursive = false;
          for (auto st : state.stack) {
            auto st_f = st.kf->function;
            if (st_f == temp_f) {
              is_recursive = true;
              break;
            }
          }
          if (is_recursive) {
            continue;
          }

          hy_log(debug, "find callee address: " + f->getName().str());
          std::uint64_t addr = legalFunctionsAddress[f];
          ref<ConstantExpr> value = ConstantExpr::create(addr, v->getWidth());
          hy_dump(-1, EqExpr::create(v, value)->print, str);
          StatePair res =
              fork(*free, EqExpr::create(v, value), true, BranchType::Call);
          if (res.first) {
            // Don't give warning on unique resolution
            if (res.second || !first)
              klee_warning_once(reinterpret_cast<void *>(addr),
                                "resolved symbolic function pointer to: %s",
                                f->getName().data());

            hy_log(debug, "resolved symbolic function pointer to: " +
                              f->getName().str());
            executeCall(*res.first, ki, f, arguments);
          }

          first = false;
          if (res.second == nullptr) {
            break;
          }
          free = res.second;
        }
      }
      if (free != nullptr) {
        terminateStateEarly(*free, "invalid state from function pointer",
                            StateTerminationType::Interrupted);
      }

      // yuhao: try function based on type
      // llvm::Type *t = fp->getType();
      // llvm::FunctionType *ft = llvm::cast<llvm::FunctionType>(
      //     llvm::cast<llvm::PointerType>(t)->getNonOpaquePointerElementType());
      // std::set<llvm::Function *> *set_function;
      // if (this->map_function_type.find(ft) == this->map_function_type.end())
      // {
      //   set_function = new std::set<llvm::Function *>;
      //   this->map_function_type[ft] = set_function;
      // } else {
      //   set_function = this->map_function_type[ft];
      // }

      // for (auto temp_f : *set_function) {
      //   f = temp_f;
      //   if (legalFunctionsAddress.find(f) == legalFunctionsAddress.end()) {
      //     continue;
      //   }
      //   std::uint64_t addr = legalFunctionsAddress[f];
      //   ref<ConstantExpr> value = ConstantExpr::create(addr, v->getWidth());
      //   hy_dump(0, EqExpr::create(v, value)->print, str);
      //   StatePair res =
      //       fork(*free, EqExpr::create(v, value), true, BranchType::Call);
      //   if (res.first) {
      //     // Don't give warning on unique resolution
      //     if (res.second || !first)
      //       klee_warning_once(reinterpret_cast<void *>(addr),
      //                         "resolved symbolic function pointer to: %s",
      //                         f->getName().data());

      //     executeCall(*res.first, ki, f, arguments);
      //   }

      //   first = false;
      //   if (res.second == nullptr) {
      //     break;
      //   }
      //   free = res.second;
      // }
      // if (free != nullptr) {
      //   terminateStateEarly(*free, "invalid state from function pointer",
      //                       StateTerminationType::Interrupted);
      // }

      // do {
      //   v = optimizer.optimizeExpr(v, true);

      //   ref<ConstantExpr> value = ConstantExpr::create(0, Expr::Bool);
      //   bool success =
      //       solver->getValue(free->constraints, v, value,
      //       free->queryMetaData);
      //   // assert(success && "FIXME: Unhandled solver failure");

      //   (void) success;
      //   StatePair res = fork(*free, EqExpr::create(v, value), true,
      //   BranchType::Call); if (res.first) {
      //     uint64_t addr = value->getZExtValue();
      //     auto it = legalFunctions.find(addr);
      //     if (it != legalFunctions.end()) {
      //       f = it->second;

      //       // Don't give warning on unique resolution
      //       if (res.second || !first)
      //         klee_warning_once(reinterpret_cast<void*>(addr),
      //                           "resolved symbolic function pointer to: %s",
      //                           f->getName().data());

      //       executeCall(*res.first, ki, f, arguments);
      //     } else {
      //       if (!hasInvalid) {
      //         terminateStateOnExecError(state, "invalid function pointer");
      //         hasInvalid = true;
      //       }
      //     }
      //   }

      //   first = false;
      //   free = res.second;
      // } while (free);
    }
    break;
  }
  case Instruction::PHI: {
    ref<Expr> result = eval(ki, state.incomingBBIndex, state).value;
    bindLocal(ki, state, result);
    break;
  }

    // Special instructions
  case Instruction::Select: {
    // NOTE: It is not required that operands 1 and 2 be of scalar type.
    ref<Expr> cond = eval(ki, 0, state).value;
    ref<Expr> tExpr = eval(ki, 1, state).value;
    ref<Expr> fExpr = eval(ki, 2, state).value;
    ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::VAArg:
    terminateStateOnExecError(state, "unexpected VAArg instruction");
    break;

    // Arithmetic / logical

  case Instruction::Add: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, AddExpr::create(left, right));
    break;
  }

  case Instruction::Sub: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, SubExpr::create(left, right));
    break;
  }

  case Instruction::Mul: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, MulExpr::create(left, right));
    break;
  }

  case Instruction::UDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;

    // yuhao: check division by zero
    if (right->isZero()) {
      terminateStateOnUserError(state, "division by zero");
      break;
    }

    ref<Expr> result = UDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;

    // yuhao: check division by zero
    if (right->isZero()) {
      terminateStateOnUserError(state, "division by zero");
      break;
    }

    ref<Expr> result = SDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::URem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = URemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SRem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SRemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::And: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AndExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Or: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = OrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Xor: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = XorExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Shl: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = ShlExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::LShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = LShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::AShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

    // Compare

  case Instruction::ICmp: {
    CmpInst *ci = cast<CmpInst>(i);
    ICmpInst *ii = cast<ICmpInst>(ci);

    switch (ii->getPredicate()) {
    case ICmpInst::ICMP_EQ: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = EqExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_NE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = NeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_UGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgtExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_UGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgtExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    default:
      terminateStateOnExecError(state, "invalid ICmp predicate");
    }
    break;
  }

    // Memory instructions...
  case Instruction::Alloca: {
    AllocaInst *ai = cast<AllocaInst>(i);
    unsigned elementSize =
        kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
    ref<Expr> size = Expr::createPointer(elementSize);
    if (ai->isArrayAllocation()) {
      ref<Expr> count = eval(ki, 0, state).value;
      count = Expr::createZExtToPointerWidth(count);
      size = MulExpr::create(size, count);
    }
    executeAlloc(state, size, true, ki);
    break;
  }

  case Instruction::Load: {
    ref<Expr> base = eval(ki, 0, state).value;

    // yuhao: debug
    if (print) {
      hy_dump(0, i->print, str);
      hy_dump(0, base->print, str);
    }

    executeMemoryOperation(state, false, base, 0, ki);

    // yuhao: record linked list
    record_linked_list(state, ki);
    break;
  }
  case Instruction::Store: {
    ref<Expr> base = eval(ki, 1, state).value;
    ref<Expr> value = eval(ki, 0, state).value;

    // yuhao: debug
    if (print) {
      hy_dump(0, i->print, str);
      hy_dump(0, value->print, str);
      hy_dump(0, base->print, str);
    }

    executeMemoryOperation(state, true, base, value, ki, 1);
    break;
  }

  case Instruction::GetElementPtr: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(ki);
    ref<Expr> base = eval(ki, 0, state).value;

    // yuhao:
    int debug = -1;
    ref<Expr> base_address = base;
    hy_log(debug,
           "size of kgepi->indices: " + std::to_string(kgepi->indices.size()));

    for (std::vector<std::pair<unsigned, uint64_t>>::iterator
             it = kgepi->indices.begin(),
             ie = kgepi->indices.end();
         it != ie; ++it) {
      uint64_t elementSize = it->second;
      ref<Expr> index = eval(ki, it->first, state).value;

      // yuhao: debug
      if (print) {
        hy_log(debug, "index: " + std::to_string(it->first));
        hy_dump(debug, index->print, str);
        hy_dump(debug, Expr::createSExtToPointerWidth(index)->print, str);
        hy_dump(debug, Expr::createPointer(elementSize)->print, str);
      }

      base = AddExpr::create(
          base, MulExpr::create(Expr::createSExtToPointerWidth(index),
                                Expr::createPointer(elementSize)));

      // yuhao: check if the index is symbolic for inbound/unbound getelementptr
      llvm::GetElementPtrInst *gep = cast<llvm::GetElementPtrInst>(i);
      if (gep->isInBounds()) {
        if (isa<ConstantExpr>(index)) {
        } else {
          hy_log(3, "getelementptr is inbounds for symbolic index");
        }
      }
    }
    if (kgepi->offset) {
      // yuhao: debug
      if (print) {
        hy_log(-1, "getelementptr offset: " +
                       std::to_string((int64_t)kgepi->offset));
      }
      base = AddExpr::create(base, Expr::createPointer(kgepi->offset));
    }

    bindLocal(ki, state, base);

    // yuhao: handle container_of
    // if the offset is negative, then it is a container_of
    // the base address would be the final address
    if (!isa<klee::ConstantExpr>(base)) {
      if (print) {
        hy_dump(-1, i->print, str);
        str = "getelementptr base address: ";
        hy_add_dump(-1, base_address->print, str);
      }

      bool is_negative = false;
      if ((int64_t)(kgepi->offset) < 0) {
        is_negative = true;
      }
      if (is_negative) {
        ref<Expr> temp = base_address;
        base_address = base;
        base = temp;
      }

      // simplify the base address
      base_address =
          ConstraintManager::simplifyExpr(state.constraints, base_address);
      base_address = optimizer.optimizeExpr(base_address, true);

      // yuhao: store inst and base address
      state.base_address[ki->inst] = base_address;
      // yuhao: store symbolic address and base address
      if (state.symbolic_address_map.find(base) !=
          state.symbolic_address_map.end()) {
        if (base_address != base) {
          state.symbolic_address_map[base] = base_address;
        }
      } else {
        state.symbolic_address_map[base] = base_address;
      }

      // yuhao: update the mo_type
      under_constrained_memory_object *ucmo =
          find_ucmo_by_base_address(state, base_address);
      if (ucmo == nullptr) {
        ucmo = create_ucmo_by_base_address(state, base_address);
      }
      llvm::GetElementPtrInst *gep =
          dyn_cast<llvm::GetElementPtrInst>(ki->inst);
      llvm::Type *type = gep->getSourceElementType();
      uint64_t size = kmodule->targetData->getTypeStoreSize(type);
      ucmo->update_ucmo_size(type, size);
    }

    break;
  }

    // Conversion
  case Instruction::Trunc: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value, 0,
                                           getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ZExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::SExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::IntToPtr: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width pType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    bindLocal(ki, state, ZExtExpr::create(arg, pType));
    break;
  }
  case Instruction::PtrToInt: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width iType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    bindLocal(ki, state, ZExtExpr::create(arg, iType));
    break;
  }

  case Instruction::BitCast: {
    ref<Expr> result = eval(ki, 0, state).value;
    bindLocal(ki, state, result);

    // yuhao: debug
    if (print) {
      hy_dump(-1, ki->inst->print, str);
    }

    int64_t debug = -1;

    // yuhao:: set type for mo in bitcast
    hy_log(debug, "BitCast: state: " + std::to_string(state.getID()));
    hy_log(debug, dump_inst(ki->inst));
    hy_dump(debug, result->print, str);
    ObjectPair op;
    bool success = get_memory_object(op, state, result);
    if (success) {
      MemoryObject *mo = const_cast<MemoryObject *>(op.first);
      hy_dump(debug, mo->getBaseExpr()->print, str);

      // yuhao: check if the offset is 0

      ref<Expr> check = EqExpr::create(mo->getBaseExpr(), result);
      check = toUnique_ucmo(state, check);
      if (check->isTrue()) {
        auto bi = dyn_cast<llvm::BitCastInst>(ki->inst);
        hy_log(debug, "BitCast: update mo type");
        add_mo_type(state, mo, bi->getSrcTy()->getPointerElementType());
        add_mo_type(state, mo, bi->getDestTy()->getPointerElementType());
      }

      // ref<Expr> offset = mo->getOffsetExpr(result);
      // ref<Expr> check = EqExpr::create(
      //     offset, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
      // check = optimizer.optimizeExpr(check, true);
      // bool inBounds;
      // solver->setTimeout(coreSolverTimeout);
      // success = solver->mustBeTrue(state.constraints, check, inBounds,
      //                              state.queryMetaData);
      // solver->setTimeout(time::Span());
      // if (success && inBounds) {
      //   auto bi = dyn_cast<llvm::BitCastInst>(ki->inst);
      //   hy_log(1, "BitCast: update mo type");
      //   add_mo_type(state, mo, bi->getSrcTy()->getPointerElementType());
      //   add_mo_type(state, mo, bi->getDestTy()->getPointerElementType());
      // }
    }

    // yuhao:: try to find the symbolic memory object
    if (!isa<ConstantExpr>(result)) {
      under_constrained_memory_object *ucmo = nullptr;
      ucmo = find_ucmo_by_base_address(state, result);
      if (ucmo == nullptr) {
        ucmo = create_ucmo_by_base_address(state, result);
      }
      llvm::BitCastInst *bi = dyn_cast<llvm::BitCastInst>(ki->inst);

      llvm::Type *src_type = bi->getSrcTy()->getPointerElementType();
      if (src_type->isSized()) {
        uint64_t src_size = kmodule->targetData->getTypeStoreSize(src_type);
        ucmo->update_ucmo_size(src_type, src_size);
      }

      llvm::Type *dest_type = bi->getDestTy()->getPointerElementType();
      if (dest_type->isSized()) {
        uint64_t dest_size = kmodule->targetData->getTypeStoreSize(dest_type);
        ucmo->update_ucmo_size(dest_type, dest_size);
      }
    }

    break;
  }

    // Floating point instructions
  case Instruction::FNeg: {
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FNeg operation");

    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    Res = llvm::neg(Res);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FAdd: {
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FAdd operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
                      left->getAPValue());
    Res.add(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()),
        APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FSub: {
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FSub operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
                      left->getAPValue());
    Res.subtract(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()),
        APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FMul: {
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FMul operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
                      left->getAPValue());
    Res.multiply(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()),
        APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FDiv: {
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FDiv operation");
    
    // yuhao: check if the right is zero
    if (right->isZero()) {
      terminateStateOnUserError(state, "division by zero");
      break;
    }

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
                      left->getAPValue());
    Res.divide(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()),
        APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FRem: {
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FRem operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
                      left->getAPValue());
    Res.mod(
        APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()));
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FPTrunc: {
    FPTruncInst *fi = cast<FPTruncInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
      return terminateStateOnExecError(state, "Unsupported FPTrunc operation");

    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven, &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPExt: {
    FPExtInst *fi = cast<FPExtInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
      return terminateStateOnExecError(state, "Unsupported FPExt operation");
    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven, &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPToUI: {
    FPToUIInst *fi = cast<FPToUIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToUI operation");

    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    uint64_t value = 0;
    bool isExact = true;
    auto valueRef = makeMutableArrayRef(value);
    Arg.convertToInteger(valueRef, resultType, false,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::FPToSI: {
    FPToSIInst *fi = cast<FPToSIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToSI operation");
    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());

    uint64_t value = 0;
    bool isExact = true;
    auto valueRef = makeMutableArrayRef(value);
    Arg.convertToInteger(valueRef, resultType, true,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::UIToFP: {
    UIToFPInst *fi = cast<UIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported UIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), false,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::SIToFP: {
    SIToFPInst *fi = cast<SIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported SIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), true,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::FCmp: {
    FCmpInst *fi = cast<FCmpInst>(i);
    ref<ConstantExpr> left =
        toConstant(state, eval(ki, 0, state).value, "floating point");
    ref<ConstantExpr> right =
        toConstant(state, eval(ki, 1, state).value, "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FCmp operation");

    APFloat LHS(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    APFloat RHS(*fpWidthToSemantics(right->getWidth()), right->getAPValue());
    APFloat::cmpResult CmpRes = LHS.compare(RHS);

    bool Result = false;
    switch (fi->getPredicate()) {
      // Predicates which only care about whether or not the operands are NaNs.
    case FCmpInst::FCMP_ORD:
      Result = (CmpRes != APFloat::cmpUnordered);
      break;

    case FCmpInst::FCMP_UNO:
      Result = (CmpRes == APFloat::cmpUnordered);
      break;

      // Ordered comparisons return false if either operand is NaN.  Unordered
      // comparisons return true if either operand is NaN.
    case FCmpInst::FCMP_UEQ:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpEqual);
      break;
    case FCmpInst::FCMP_OEQ:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpEqual);
      break;

    case FCmpInst::FCMP_UGT:
      Result = (CmpRes == APFloat::cmpUnordered ||
                CmpRes == APFloat::cmpGreaterThan);
      break;
    case FCmpInst::FCMP_OGT:
      Result = (CmpRes != APFloat::cmpUnordered &&
                CmpRes == APFloat::cmpGreaterThan);
      break;

    case FCmpInst::FCMP_UGE:
      Result =
          (CmpRes == APFloat::cmpUnordered ||
           (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
      break;
    case FCmpInst::FCMP_OGE:
      Result =
          (CmpRes != APFloat::cmpUnordered &&
           (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
      break;

    case FCmpInst::FCMP_ULT:
      Result =
          (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpLessThan);
      break;
    case FCmpInst::FCMP_OLT:
      Result =
          (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpLessThan);
      break;

    case FCmpInst::FCMP_ULE:
      Result =
          (CmpRes == APFloat::cmpUnordered ||
           (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
      break;
    case FCmpInst::FCMP_OLE:
      Result =
          (CmpRes != APFloat::cmpUnordered &&
           (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
      break;

    case FCmpInst::FCMP_UNE:
      Result = (CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual);
      break;
    case FCmpInst::FCMP_ONE:
      Result = (CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual);
      break;

    default:
      assert(0 && "Invalid FCMP predicate!");
      break;
    case FCmpInst::FCMP_FALSE:
      Result = false;
      break;
    case FCmpInst::FCMP_TRUE:
      Result = true;
      break;
    }

    bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
    break;
  }
  case Instruction::InsertValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;
    ref<Expr> val = eval(ki, 1, state).value;

    ref<Expr> l = NULL, r = NULL;
    unsigned lOffset = kgepi->offset * 8,
             rOffset = kgepi->offset * 8 + val->getWidth();

    if (lOffset > 0)
      l = ExtractExpr::create(agg, 0, lOffset);
    if (rOffset < agg->getWidth())
      r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

    ref<Expr> result;
    if (l && r)
      result = ConcatExpr::create(r, ConcatExpr::create(val, l));
    else if (l)
      result = ConcatExpr::create(val, l);
    else if (r)
      result = ConcatExpr::create(r, val);
    else
      result = val;

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ExtractValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;

    ref<Expr> result = ExtractExpr::create(agg, kgepi->offset * 8,
                                           getWidthForLLVMType(i->getType()));

    bindLocal(ki, state, result);

    // yuhao: debug
    str = "ExtractValue: ";
    hy_add_dump(-1, result->print, str);

    break;
  }
  case Instruction::Fence: {
    // Ignore for now
    break;
  }
  case Instruction::InsertElement: {
    InsertElementInst *iei = cast<InsertElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> newElt = eval(ki, 1, state).value;
    ref<Expr> idx = eval(ki, 2, state).value;

    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnExecError(
          state, "InsertElement, support for symbolic index not implemented");
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
#if LLVM_VERSION_MAJOR >= 11
    const auto *vt = cast<llvm::FixedVectorType>(iei->getType());
#else
    const llvm::VectorType *vt = iei->getType();
#endif
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds write
      terminateStateOnProgramError(state,
                                   "Out of bounds write when inserting element",
                                   StateTerminationType::BadVectorAccess);
      return;
    }

    const unsigned elementCount = vt->getNumElements();
    llvm::SmallVector<ref<Expr>, 8> elems;
    elems.reserve(elementCount);
    for (unsigned i = elementCount; i != 0; --i) {
      auto of = i - 1;
      unsigned bitOffset = EltBits * of;
      elems.push_back(
          of == iIdx ? newElt : ExtractExpr::create(vec, bitOffset, EltBits));
    }

    assert(Context::get().isLittleEndian() && "FIXME:Broken for big endian");
    ref<Expr> Result = ConcatExpr::createN(elementCount, elems.data());
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ExtractElement: {
    ExtractElementInst *eei = cast<ExtractElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> idx = eval(ki, 1, state).value;

    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnExecError(
          state, "ExtractElement, support for symbolic index not implemented");
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
#if LLVM_VERSION_MAJOR >= 11
    const auto *vt = cast<llvm::FixedVectorType>(eei->getVectorOperandType());
#else
    const llvm::VectorType *vt = eei->getVectorOperandType();
#endif
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds read
      terminateStateOnProgramError(state,
                                   "Out of bounds read when extracting element",
                                   StateTerminationType::BadVectorAccess);
      return;
    }

    unsigned bitOffset = EltBits * iIdx;
    ref<Expr> Result = ExtractExpr::create(vec, bitOffset, EltBits);
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ShuffleVector:
    // Should never happen due to Scalarizer pass removing ShuffleVector
    // instructions.
    terminateStateOnExecError(state, "Unexpected ShuffleVector instruction");
    break;

#ifdef SUPPORT_KLEE_EH_CXX
  case Instruction::Resume: {
    auto *cui = dyn_cast_or_null<CleanupPhaseUnwindingInformation>(
        state.unwindingInformation.get());

    if (!cui) {
      terminateStateOnExecError(
          state,
          "resume-instruction executed outside of cleanup phase unwinding");
      break;
    }

    ref<Expr> arg = eval(ki, 0, state).value;
    ref<Expr> exceptionPointer = ExtractExpr::create(arg, 0, Expr::Int64);
    ref<Expr> selectorValue =
        ExtractExpr::create(arg, Expr::Int64, Expr::Int32);

    if (!dyn_cast<ConstantExpr>(exceptionPointer) ||
        !dyn_cast<ConstantExpr>(selectorValue)) {
      terminateStateOnExecError(
          state, "resume-instruction called with non constant expression");
      break;
    }

    if (!Expr::createIsZero(selectorValue)->isTrue()) {
      klee_warning("resume-instruction called with non-0 selector value");
    }

    if (!EqExpr::create(exceptionPointer, cui->exceptionObject)->isTrue()) {
      terminateStateOnExecError(
          state, "resume-instruction called with unexpected exception pointer");
      break;
    }

    unwindToNextLandingpad(state);
    break;
  }

  case Instruction::LandingPad: {
    auto *cui = dyn_cast_or_null<CleanupPhaseUnwindingInformation>(
        state.unwindingInformation.get());

    if (!cui) {
      terminateStateOnExecError(
          state, "Executing landing pad but not in unwinding phase 2");
      break;
    }

    ref<ConstantExpr> exceptionPointer = cui->exceptionObject;
    ref<ConstantExpr> selectorValue;

    // check on which frame we are currently
    if (state.stack.size() - 1 == cui->catchingStackIndex) {
      // we are in the target stack frame, return the selector value
      // that was returned by the personality fn in phase 1 and stop unwinding.
      selectorValue = cui->selectorValue;

      // stop unwinding by cleaning up our unwinding information.
      state.unwindingInformation.reset();

      // this would otherwise now be a dangling pointer
      cui = nullptr;
    } else {
      // we are not yet at the target stack frame. the landingpad might have
      // a cleanup clause or not, anyway, we give it the selector value "0",
      // which represents a cleanup, and expect it to handle it.
      // This is explicitly allowed by LLVM, see
      // https://llvm.org/docs/ExceptionHandling.html#id18
      selectorValue = ConstantExpr::create(0, Expr::Int32);
    }

    // we have to return a {i8*, i32}
    ref<Expr> result = ConcatExpr::create(
        ZExtExpr::create(selectorValue, Expr::Int32), exceptionPointer);

    bindLocal(ki, state, result);

    break;
  }
#endif // SUPPORT_KLEE_EH_CXX

  case Instruction::AtomicRMW:
    terminateStateOnExecError(state, "Unexpected Atomic instruction, should be "
                                     "lowered by LowerAtomicInstructionPass");
    break;
  case Instruction::AtomicCmpXchg:
    terminateStateOnExecError(state,
                              "Unexpected AtomicCmpXchg instruction, should be "
                              "lowered by LowerAtomicInstructionPass");
    break;
  // Other instructions...
  // Unhandled
  default:
    terminateStateOnExecError(state, "illegal instruction");
    break;
  }
}

void Executor::updateStates(ExecutionState *current) {
  if (searcher) {
    searcher->update(current, addedStates, removedStates);
  }

  states.insert(addedStates.begin(), addedStates.end());
  addedStates.clear();

  for (std::vector<ExecutionState *>::iterator it = removedStates.begin(),
                                               ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    std::set<ExecutionState *>::iterator it2 = states.find(es);
    assert(it2 != states.end());
    states.erase(it2);
    std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it3 =
        seedMap.find(es);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    processTree->remove(es->ptreeNode);
    delete es;
  }
  removedStates.clear();
}

template <typename TypeIt>
void Executor::computeOffsetsSeqTy(KGEPInstruction *kgepi,
                                   ref<ConstantExpr> &constantOffset,
                                   uint64_t index, const TypeIt it) {
  assert(it->getNumContainedTypes() == 1 &&
         "Sequential type must contain one subtype");
  uint64_t elementSize =
      kmodule->targetData->getTypeStoreSize(it->getContainedType(0));
  const Value *operand = it.getOperand();
  if (const Constant *c = dyn_cast<Constant>(operand)) {
    ref<ConstantExpr> index =
        evalConstant(c)->SExt(Context::get().getPointerWidth());
    ref<ConstantExpr> addend = index->Mul(
        ConstantExpr::alloc(elementSize, Context::get().getPointerWidth()));
    constantOffset = constantOffset->Add(addend);
  } else {
    kgepi->indices.emplace_back(index, elementSize);
  }
}

template <typename TypeIt>
void Executor::computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie) {
  ref<ConstantExpr> constantOffset =
      ConstantExpr::alloc(0, Context::get().getPointerWidth());
  uint64_t index = 1;
  for (TypeIt ii = ib; ii != ie; ++ii) {
    if (StructType *st = dyn_cast<StructType>(*ii)) {
      const StructLayout *sl = kmodule->targetData->getStructLayout(st);
      const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
      uint64_t addend = sl->getElementOffset((unsigned)ci->getZExtValue());
      constantOffset = constantOffset->Add(
          ConstantExpr::alloc(addend, Context::get().getPointerWidth()));
    } else if (ii->isArrayTy() || ii->isVectorTy() || ii->isPointerTy()) {
      computeOffsetsSeqTy(kgepi, constantOffset, index, ii);
    } else
      assert("invalid type" && 0);
    index++;
  }
  kgepi->offset = constantOffset->getZExtValue();
}

void Executor::bindInstructionConstants(KInstruction *KI) {
  if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, gep_type_begin(gepi), gep_type_end(gepi));
  } else if (InsertValueInst *ivi = dyn_cast<InsertValueInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, iv_type_begin(ivi), iv_type_end(ivi));
    assert(kgepi->indices.empty() && "InsertValue constant offset expected");
  } else if (ExtractValueInst *evi = dyn_cast<ExtractValueInst>(KI->inst)) {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction *>(KI);
    computeOffsets(kgepi, ev_type_begin(evi), ev_type_end(evi));
    assert(kgepi->indices.empty() && "ExtractValue constant offset expected");
  }
}

void Executor::bindModuleConstants() {
  for (auto &kfp : kmodule->functions) {
    KFunction *kf = kfp.get();
    for (unsigned i = 0; i < kf->numInstructions; ++i)
      bindInstructionConstants(kf->instructions[i]);
  }

  kmodule->constantTable =
      std::unique_ptr<Cell[]>(new Cell[kmodule->constants.size()]);
  for (unsigned i = 0; i < kmodule->constants.size(); ++i) {
    Cell &c = kmodule->constantTable[i];
    c.value = evalConstant(kmodule->constants[i]);
  }
}

bool Executor::checkMemoryUsage() {
  if (!MaxMemory)
    return true;

  // We need to avoid calling GetTotalMallocUsage() often because it
  // is O(elts on freelist). This is really bad since we start
  // to pummel the freelist once we hit the memory cap.
  if ((stats::instructions & 0xFFFFU) != 0) // every 65536 instructions
    return true;

  // check memory limit
  const auto mallocUsage = util::GetTotalMallocUsage() >> 20U;
  const auto mmapUsage = memory->getUsedDeterministicSize() >> 20U;
  const auto totalUsage = mallocUsage + mmapUsage;
  atMemoryLimit = totalUsage > MaxMemory; // inhibit forking
  if (!atMemoryLimit)
    return true;

  // only terminate states when threshold (+100MB) exceeded
  if (totalUsage <= MaxMemory + 100)
    return true;

  // just guess at how many to kill
  const auto numStates = states.size();
  auto toKill = std::max(1UL, numStates - numStates * MaxMemory / totalUsage);
  klee_warning("killing %lu states (over memory cap: %luMB)", toKill,
               totalUsage);

  // randomly select states for early termination
  std::vector<ExecutionState *> arr(states.begin(),
                                    states.end()); // FIXME: expensive
  for (unsigned i = 0, N = arr.size(); N && i < toKill; ++i, --N) {
    unsigned idx = theRNG.getInt32() % N;
    // Make two pulls to try and not hit a state that
    // covered new code.
    if (arr[idx]->coveredNew)
      idx = theRNG.getInt32() % N;

    std::swap(arr[idx], arr[N - 1]);
    terminateStateEarly(*arr[N - 1], "Memory limit exceeded.",
                        StateTerminationType::OutOfMemory);
  }

  return false;
}

void Executor::doDumpStates() {
  if (!DumpStatesOnHalt || states.empty()) {
    interpreterHandler->incPathsExplored(states.size());
    return;
  }

  klee_message("halting execution, dumping remaining states");
  for (const auto &state : states)
    terminateStateEarly(*state, "Execution halting.",
                        StateTerminationType::Interrupted);
  updateStates(nullptr);
}

void Executor::run(ExecutionState &initialState) {
  // bindModuleConstants();

  // Delay init till now so that ticks don't accrue during optimization and
  // such.
  timers.reset();

  states.insert(&initialState);

  if (usingSeeds) {
    std::vector<SeedInfo> &v = seedMap[&initialState];

    for (std::vector<KTest *>::const_iterator it = usingSeeds->begin(),
                                              ie = usingSeeds->end();
         it != ie; ++it)
      v.push_back(SeedInfo(*it));

    int lastNumSeeds = usingSeeds->size() + 10;
    time::Point lastTime, startTime = lastTime = time::getWallTime();
    ExecutionState *lastState = 0;
    while (!seedMap.empty()) {
      if (haltExecution) {
        doDumpStates();
        return;
      }

      std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
          seedMap.upper_bound(lastState);
      if (it == seedMap.end())
        it = seedMap.begin();
      lastState = it->first;
      ExecutionState &state = *lastState;
      KInstruction *ki = state.pc;
      stepInstruction(state);

      executeInstruction(state, ki);
      timers.invoke();
      if (::dumpStates)
        dumpStates();
      if (::dumpPTree)
        dumpPTree();
      updateStates(&state);

      if ((stats::instructions % 1000) == 0) {
        int numSeeds = 0, numStates = 0;
        for (std::map<ExecutionState *, std::vector<SeedInfo>>::iterator
                 it = seedMap.begin(),
                 ie = seedMap.end();
             it != ie; ++it) {
          numSeeds += it->second.size();
          numStates++;
        }
        const auto time = time::getWallTime();
        const time::Span seedTime(SeedTime);
        if (seedTime && time > startTime + seedTime) {
          klee_warning("seed time expired, %d seeds remain over %d states",
                       numSeeds, numStates);
          break;
        } else if (numSeeds <= lastNumSeeds - 10 ||
                   time - lastTime >= time::seconds(10)) {
          lastTime = time;
          lastNumSeeds = numSeeds;
          klee_message("%d seeds remaining over: %d states", numSeeds,
                       numStates);
        }
      }
    }

    klee_message("seeding done (%d states remain)", (int)states.size());

    if (OnlySeed) {
      doDumpStates();
      return;
    }
  }

  searcher = constructUserSearcher(*this);

  std::vector<ExecutionState *> newStates(states.begin(), states.end());
  searcher->update(0, newStates, std::vector<ExecutionState *>());

  // main interpreter loop
  while (!states.empty() && !haltExecution) {
    ExecutionState &state = searcher->selectState();
    KInstruction *ki = state.pc;
    stepInstruction(state);

    executeInstruction(state, ki);
    timers.invoke();
    if (::dumpStates)
      dumpStates();
    if (::dumpPTree)
      dumpPTree();

    updateStates(&state);

    if (!checkMemoryUsage()) {
      // update searchers when states were terminated early due to memory
      // pressure
      updateStates(nullptr);
    }
  }

  delete searcher;
  searcher = nullptr;

  doDumpStates();
}

std::string Executor::getAddressInfo(ExecutionState &state,
                                     ref<Expr> address) const {
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    example = CE->getZExtValue();
  } else {

    // yuhao:
    ref<ConstantExpr> value = ConstantExpr::create(0, address->getWidth());
    solver->setTimeout(coreSolverTimeout);
    bool success = solver->getValue(state.constraints, address, value,
                                    state.queryMetaData);
    // assert(success && "FIXME: Unhandled solver failure");

    (void)success;
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair<ref<Expr>, ref<Expr>> res =
        solver->getRange(state.constraints, address, state.queryMetaData);
    info << "\trange: [" << res.first << ", " << res.second << "]\n";
    solver->setTimeout(time::Span());
  }

  MemoryObject hack((unsigned)example);
  MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower == state.addressSpace.objects.end()) {
    info << "none\n";
  } else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address << " of size " << mo->size << "\n"
         << "\t\t" << alloc_info << "\n";
  }
  if (lower != state.addressSpace.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower == state.addressSpace.objects.end()) {
      info << "none\n";
    } else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address << " of size " << mo->size << "\n"
           << "\t\t" << alloc_info << "\n";
    }
  }

  return info.str();
}

void Executor::terminateState(ExecutionState &state) {

  // yuhao: output arguments
  if (state.specification) {
    uint64_t ret = specification_handle(state);
    update_fork_points(state, ret);
  }

  if (replayKTest && replayPosition != replayKTest->numObjects) {
    klee_warning_once(replayKTest,
                      "replay did not consume all objects in test input.");
  }

  interpreterHandler->incPathsExplored();

  std::vector<ExecutionState *>::iterator it =
      std::find(addedStates.begin(), addedStates.end(), &state);
  if (it == addedStates.end()) {
    state.pc = state.prevPC;

    removedStates.push_back(&state);
  } else {
    // never reached searcher, just delete immediately
    std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it3 =
        seedMap.find(&state);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    addedStates.erase(it);
    processTree->remove(state.ptreeNode);
    delete &state;
  }
}

static bool shouldWriteTest(const ExecutionState &state) {
  return !OnlyOutputStatesCoveringNew || state.coveredNew;
}

static std::string terminationTypeFileExtension(StateTerminationType type) {
  std::string ret;
#undef TTYPE
#undef TTMARK
#define TTYPE(N, I, S)                                                         \
  case StateTerminationType::N:                                                \
    ret = (S);                                                                 \
    break;
#define TTMARK(N, I)
  switch (type) { TERMINATION_TYPES }
  return ret;
};

void Executor::terminateStateOnExit(ExecutionState &state) {
  ++stats::terminationExit;
  if (shouldWriteTest(state) || (AlwaysOutputSeeds && seedMap.count(&state)))
    interpreterHandler->processTestCase(
        state, nullptr,
        terminationTypeFileExtension(StateTerminationType::Exit).c_str());

  interpreterHandler->incPathsCompleted();
  state.completed = true;
  terminateState(state);
}

void Executor::terminateStateEarly(ExecutionState &state, const Twine &message,
                                   StateTerminationType reason) {
  if (reason <= StateTerminationType::EARLY) {
    assert(reason > StateTerminationType::EXIT);
    ++stats::terminationEarly;
  }

  if ((reason <= StateTerminationType::EARLY && shouldWriteTest(state)) ||
      (AlwaysOutputSeeds && seedMap.count(&state))) {
    interpreterHandler->processTestCase(
        state, (message + "\n").str().c_str(),
        terminationTypeFileExtension(reason).c_str());
  }

  // yuhao:
  terminateStateOnError(state, message, reason);
}

void Executor::terminateStateEarlyAlgorithm(ExecutionState &state,
                                            const llvm::Twine &message,
                                            StateTerminationType reason) {
  assert(reason > StateTerminationType::EXECERR &&
         reason <= StateTerminationType::EARLYALGORITHM);
  ++stats::terminationEarlyAlgorithm;
  terminateStateEarly(state, message, reason);
}

void Executor::terminateStateEarlyUser(ExecutionState &state,
                                       const llvm::Twine &message) {
  ++stats::terminationEarlyUser;
  terminateStateEarly(state, message, StateTerminationType::SilentExit);
}

const InstructionInfo &
Executor::getLastNonKleeInternalInstruction(const ExecutionState &state,
                                            Instruction **lastInstruction) {
  // unroll the stack of the applications state and find
  // the last instruction which is not inside a KLEE internal function
  ExecutionState::stack_ty::const_reverse_iterator it = state.stack.rbegin(),
                                                   itE = state.stack.rend();

  // don't check beyond the outermost function (i.e. main())
  itE--;

  const InstructionInfo *ii = 0;
  if (kmodule->internalFunctions.count(it->kf->function) == 0) {
    ii = state.prevPC->info;
    *lastInstruction = state.prevPC->inst;
    //  Cannot return yet because even though
    //  it->function is not an internal function it might of
    //  been called from an internal function.
  }

  // Wind up the stack and check if we are in a KLEE internal function.
  // We visit the entire stack because we want to return a CallInstruction
  // that was not reached via any KLEE internal functions.
  for (; it != itE; ++it) {
    // check calling instruction and if it is contained in a KLEE internal
    // function
    const Function *f = (*it->caller).inst->getParent()->getParent();
    if (kmodule->internalFunctions.count(f)) {
      ii = 0;
      continue;
    }
    if (!ii) {
      ii = (*it->caller).info;
      *lastInstruction = (*it->caller).inst;
    }
  }

  if (!ii) {
    // something went wrong, play safe and return the current instruction info
    *lastInstruction = state.prevPC->inst;
    return *state.prevPC->info;
  }
  return *ii;
}

bool shouldExitOn(StateTerminationType reason) {
  auto it = std::find(ExitOnErrorType.begin(), ExitOnErrorType.end(), reason);
  return it != ExitOnErrorType.end();
}

void Executor::terminateStateOnError(ExecutionState &state,
                                     const llvm::Twine &messaget,
                                     StateTerminationType terminationType,
                                     const llvm::Twine &info,
                                     const char *suffix) {
  std::string message = messaget.str();
  static std::set<std::pair<Instruction *, std::string>> emittedErrors;
  Instruction *lastInst;
  const InstructionInfo &ii =
      getLastNonKleeInternalInstruction(state, &lastInst);

  // yuhao: debug
  std::string str;
  str += "terminateStateOnError: " + std::to_string(state.getID()) + ": " +
         message + "\n";
  hy_add(-1, state.dumpStack, str);
  hy_log(-1, str);

  if (EmitAllErrors ||
      emittedErrors.insert(std::make_pair(lastInst, message)).second) {
    if (!ii.file.empty()) {
      klee_message("ERROR: %s:%d: %s", ii.file.c_str(), ii.line,
                   message.c_str());
    } else {
      klee_message("ERROR: (location information missing) %s", message.c_str());
    }
    if (!EmitAllErrors)
      klee_message("NOTE: now ignoring this error at this location");

    std::string MsgString;
    llvm::raw_string_ostream msg(MsgString);
    msg << "Error: " << message << '\n';
    if (!ii.file.empty()) {
      msg << "File: " << ii.file << '\n'
          << "Line: " << ii.line << '\n'
          << "assembly.ll line: " << ii.assemblyLine << '\n'
          << "State: " << state.getID() << '\n';
    }
    msg << "Stack: \n";
    state.dumpStack(msg);

    std::string info_str = info.str();
    if (!info_str.empty())
      msg << "Info: \n" << info_str;

    const std::string ext = terminationTypeFileExtension(terminationType);
    // use user provided suffix from klee_report_error()
    const char *file_suffix = suffix ? suffix : ext.c_str();
    interpreterHandler->processTestCase(state, msg.str().c_str(), file_suffix);
  }

  terminateState(state);

  if (shouldExitOn(terminationType))
    haltExecution = true;
}

void Executor::terminateStateOnExecError(ExecutionState &state,
                                         const llvm::Twine &message,
                                         StateTerminationType reason) {
  assert(reason > StateTerminationType::USERERR &&
         reason <= StateTerminationType::EXECERR);
  ++stats::terminationExecutionError;
  terminateStateOnError(state, message, reason, "");
}

void Executor::terminateStateOnProgramError(ExecutionState &state,
                                            const llvm::Twine &message,
                                            StateTerminationType reason,
                                            const llvm::Twine &info,
                                            const char *suffix) {
  assert(reason > StateTerminationType::SOLVERERR &&
         reason <= StateTerminationType::PROGERR);
  ++stats::terminationProgramError;
  terminateStateOnError(state, message, reason, info, suffix);
}

void Executor::terminateStateOnSolverError(ExecutionState &state,
                                           const llvm::Twine &message) {
  ++stats::terminationSolverError;
  terminateStateOnError(state, message, StateTerminationType::Solver, "");
}

void Executor::terminateStateOnUserError(ExecutionState &state,
                                         const llvm::Twine &message) {
  ++stats::terminationUserError;
  terminateStateOnError(state, message, StateTerminationType::User, "");
}

// XXX shoot me
static const char *okExternalsList[] = {"printf", "fprintf", "puts", "getpid"};
static std::set<std::string> okExternals(
    okExternalsList,
    okExternalsList + (sizeof(okExternalsList) / sizeof(okExternalsList[0])));

void Executor::callExternalFunction(ExecutionState &state, KInstruction *target,
                                    KCallable *callable,
                                    std::vector<ref<Expr>> &arguments) {
  // check if specialFunctionHandler wants it
  if (const auto *func = dyn_cast<KFunction>(callable)) {
    if (specialFunctionHandler->handle(state, func->function, target,
                                       arguments))
      return;
  }

  if (ExternalCalls == ExternalCallPolicy::None &&
      !okExternals.count(callable->getName().str())) {
    // yuhao:
    // klee_warning("Disallowed call to external function: %s\n",
    //            callable->getName().str().c_str());
    // terminateStateOnUserError(state, "external calls disallowed");
    llvm::Type *returnType = target->inst->getType();
    if (!returnType->isVoidTy()) {
      std::string symbolic_name =
          get_symbolic_name(external_return_name, external_return_count);
      unsigned int type_store_size =
          kmodule->targetData->getTypeStoreSize(returnType);
      klee::Expr::Width type_load_size = getWidthForLLVMType(returnType);
      klee::ref<klee::Expr> symbolic = klee::Executor::manual_make_symbolic(
          state, symbolic_name, target->inst, type_store_size, type_load_size,
          returnType);
      bindLocal(target, state, symbolic);

      std::string str;
      str = "";
      str += "make external return: " + symbolic_name + "\n";
      hy_add(-1, target->inst->print, str);
      str += "\n";
      hy_add(-1, state.dumpStack, str);
      hy_log(-1, str);
    }

    return;
  }

  // normal external function handling path
  // allocate 512 bits for each argument (+return value) to support
  // fp80's and SIMD vectors as parameters for external calls;
  // we could iterate through all the arguments first and determine the exact
  // size we need, but this is faster, and the memory usage isn't significant.
  size_t allocatedBytes = Expr::MaxWidth / 8 * (arguments.size() + 1);
  uint64_t *args = (uint64_t *)alloca(allocatedBytes);
  memset(args, 0, allocatedBytes);
  unsigned wordIndex = 2;
  for (std::vector<ref<Expr>>::iterator ai = arguments.begin(),
                                        ae = arguments.end();
       ai != ae; ++ai) {
    if (ExternalCalls ==
        ExternalCallPolicy::All) { // don't bother checking uniqueness
      *ai = optimizer.optimizeExpr(*ai, true);

      // yuhao:
      ref<ConstantExpr> ce = ConstantExpr::create(0, Expr::Int64);
      // solver->setTimeout(coreSolverTimeout);
      bool success =
          solver->getValue(state.constraints, *ai, ce, state.queryMetaData);
      // assert(success && "FIXME: Unhandled solver failure");
      // solver->setTimeout(time::Span());

      (void)success;
      ce->toMemory(&args[wordIndex]);
      ObjectPair op;
      // Checking to see if the argument is a pointer to something
      if (ce->getWidth() == Context::get().getPointerWidth() &&
          state.addressSpace.resolveOne(ce, op)) {
        op.second->flushToConcreteStore(solver.get(), state);
      }
      wordIndex += (ce->getWidth() + 63) / 64;
    } else {
      ref<Expr> arg = toUnique(state, *ai);
      if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
        // fp80 must be aligned to 16 according to the System V AMD 64 ABI
        if (ce->getWidth() == Expr::Fl80 && wordIndex & 0x01)
          wordIndex++;

        // XXX kick toMemory functions from here
        ce->toMemory(&args[wordIndex]);
        wordIndex += (ce->getWidth() + 63) / 64;
      } else {
        terminateStateOnExecError(state,
                                  "external call with symbolic argument: " +
                                      callable->getName());
        return;
      }
    }
  }

  // Prepare external memory for invoking the function
  static std::size_t residentPages = 0;
  double avgNeededPages = 0;
  if (MemoryManager::isDeterministic) {
    auto const minflt = [] {
      struct rusage ru = {};
      [[maybe_unused]] int ret = getrusage(RUSAGE_SELF, &ru);
      assert(!ret && "getrusage failed");
      assert(ru.ru_minflt >= 0);
      return ru.ru_minflt;
    };

    auto tmp = minflt();
    std::size_t neededPages = state.addressSpace.copyOutConcretes();
    auto newPages = minflt() - tmp;
    assert(newPages >= 0);
    residentPages += newPages;
    assert(residentPages >= neededPages &&
           "allocator too full, assumption that each object occupies its own "
           "page is no longer true");

    // average of pages needed for an external function call
    static double avgNeededPages_ = residentPages;
    // exponential moving average with alpha = 1/3
    avgNeededPages_ = (3.0 * avgNeededPages_ + neededPages) / 4.0;
    avgNeededPages = avgNeededPages_;
  } else {
    state.addressSpace.copyOutConcretes();
  }

#ifndef WINDOWS
  // Update external errno state with local state value
  int *errno_addr = getErrnoLocation(state);
  ObjectPair result;
  bool resolved = state.addressSpace.resolveOne(
      ConstantExpr::create((uint64_t)errno_addr, Expr::Int64), result);
  if (!resolved)
    klee_error("Could not resolve memory object for errno");
  ref<Expr> errValueExpr = result.second->read(0, sizeof(*errno_addr) * 8);
  ConstantExpr *errnoValue = dyn_cast<ConstantExpr>(errValueExpr);
  if (!errnoValue) {
    terminateStateOnExecError(state,
                              "external call with errno value symbolic: " +
                                  callable->getName());
    return;
  }

  externalDispatcher->setLastErrno(
      errnoValue->getZExtValue(sizeof(*errno_addr) * 8));
#endif

  if (!SuppressExternalWarnings) {

    std::string TmpStr;
    llvm::raw_string_ostream os(TmpStr);
    os << "calling external: " << callable->getName().str() << "(";
    for (unsigned i = 0; i < arguments.size(); i++) {
      os << arguments[i];
      if (i != arguments.size() - 1)
        os << ", ";
    }
    os << ") at " << state.pc->getSourceLocation();

    if (AllExternalWarnings)
      klee_warning("%s", os.str().c_str());
    else
      klee_warning_once(callable->getValue(), "%s", os.str().c_str());
  }

  bool success = externalDispatcher->executeCall(callable, target->inst, args);
  if (!success) {
    terminateStateOnExecError(state,
                              "failed external call: " + callable->getName(),
                              StateTerminationType::External);
    return;
  }

  if (!state.addressSpace.copyInConcretes()) {
    terminateStateOnExecError(state, "external modified read-only object",
                              StateTerminationType::External);
    return;
  }

  if (MemoryManager::isDeterministic && residentPages > ExternalPageThreshold &&
      residentPages > 2 * avgNeededPages) {
    if (memory->markMappingsAsUnneeded()) {
      residentPages = 0;
    }
  }

#ifndef WINDOWS
  // Update errno memory object with the errno value from the call
  int error = externalDispatcher->getLastErrno();
  state.addressSpace.copyInConcrete(result.first, result.second,
                                    (uint64_t)&error);
#endif

  Type *resultType = target->inst->getType();
  if (resultType != Type::getVoidTy(kmodule->module->getContext())) {
    ref<Expr> e =
        ConstantExpr::fromMemory((void *)args, getWidthForLLVMType(resultType));
    bindLocal(target, state, e);
  }
}

/***/

ref<Expr> Executor::replaceReadWithSymbolic(ExecutionState &state,
                                            ref<Expr> e) {
  unsigned n = interpreterOpts.MakeConcreteSymbolic;
  if (!n || replayKTest || replayPath)
    return e;

  // right now, we don't replace symbolics (is there any reason to?)
  if (!isa<ConstantExpr>(e))
    return e;

  if (n != 1 && random() % n)
    return e;

  // create a new fresh location, assert it is equal to concrete value in e
  // and return it.

  static unsigned id;
  const Array *array =
      arrayCache.CreateArray("rrws_arr" + llvm::utostr(++id),
                             Expr::getMinBytesForWidth(e->getWidth()));
  ref<Expr> res = Expr::createTempRead(array, e->getWidth());
  ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, res));
  llvm::errs() << "Making symbolic: " << eq << "\n";
  state.addConstraint(eq);
  return res;
}

ObjectState *Executor::bindObjectInState(ExecutionState &state,
                                         const MemoryObject *mo, bool isLocal,
                                         const Array *array) {
  ObjectState *os = array ? new ObjectState(mo, array) : new ObjectState(mo);
  state.addressSpace.bindObject(mo, os);

  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object
  // on function return.
  if (isLocal)
    state.stack.back().allocas.push_back(mo);

  return os;
}

void Executor::executeAlloc(ExecutionState &state, ref<Expr> size, bool isLocal,
                            KInstruction *target, bool zeroMemory,
                            const ObjectState *reallocFrom,
                            size_t allocationAlignment) {
  size = toUnique(state, size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
    const llvm::Value *allocSite = state.prevPC->inst;
    if (allocationAlignment == 0) {
      allocationAlignment = getAllocationAlignment(allocSite);
    }
    MemoryObject *mo =
        memory->allocate(CE->getZExtValue(), isLocal, /*isGlobal=*/false,
                         &state, allocSite, allocationAlignment);
    if (!mo) {
      bindLocal(target, state,
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {

      // yuhao: set type for mo in alloc inst
      if (auto ai = dyn_cast<llvm::AllocaInst>(target->inst)) {
        // std::string str;
        // hy_dump(0, ai->print, str);
        // hy_dump(0, ai->getAllocatedType()->print, str);
        add_mo_type(state, mo, ai->getAllocatedType());
      }

      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory) {
        os->initializeToZero();
      } else {
        os->initializeToRandom();
      }
      bindLocal(target, state, mo->getBaseExpr());

      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i = 0; i < count; i++)
          os->write(i, reallocFrom->read8(i));
        const MemoryObject *reallocObject = reallocFrom->getObject();
        state.deallocate(reallocObject);
        state.addressSpace.unbindObject(reallocObject);
      }
    }
  } else {
    // yuhao: alloc ucmo instead of mo, so we can resize the mo when necessary
    // for the initial size, we pick a may value close to 1024

    std::string symbolic_name = get_symbolic_name(alloc_name, alloc_count);
    llvm::Type *returnType = target->inst->getType();
    klee::ref<klee::Expr> symbolic_address =
        klee::Executor::manual_make_symbolic(state, symbolic_name, target->inst,
                                             Context::get().getPointerWidth(),
                                             Context::get().getPointerWidth(),
                                             returnType);
    under_constrained_memory_object *ucmo = nullptr;
    ucmo = create_ucmo_by_base_address(state, symbolic_address);

    size = optimizer.optimizeExpr(size, true);
    ucmo->update_ucmo_symbolic_size(size);

    ref<ConstantExpr> example = ConstantExpr::create(0, size->getWidth());

    solver->setTimeout(coreSolverTimeout);
    bool success =
        solver->getValue(state.constraints, size, example, state.queryMetaData);
    (void)success;
    solver->setTimeout(time::Span());

    // Try and start with a small example.
    Expr::Width W = example->getWidth();
    solver->setTimeout(coreSolverTimeout);
    while (example->Ugt(ConstantExpr::alloc(4096, W))->isTrue()) {
      ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(4, W));
      bool res;
      bool success =
          solver->mayBeTrue(state.constraints, EqExpr::create(tmp, size), res,
                            state.queryMetaData);

      (void)success;
      if (!success || !res)
        break;
      example = tmp;
    }
    // while (example->Ult(ConstantExpr::alloc(512, W))->isTrue()) {
    //   ref<ConstantExpr> tmp = example->Shl(ConstantExpr::alloc(1, W));
    //   bool res;
    //   bool success =
    //       solver->mayBeTrue(state.constraints, EqExpr::create(tmp, size), res,
    //                         state.queryMetaData);

    //   (void)success;
    //   if (!success || !res)
    //     break;
    //   example = tmp;
    // }
    solver->setTimeout(time::Span());

    const llvm::Value *allocSite = state.prevPC->inst;
    if (allocationAlignment == 0) {
      allocationAlignment = getAllocationAlignment(allocSite);
    }
    MemoryObject *mo =
        memory->allocate(example->getZExtValue(), false, /*isGlobal=*/false,
                         &state, allocSite, allocationAlignment);
    if (!mo) {
      bindLocal(target, state,
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {

      // yuhao: update smo info
      ucmo->update_ucmo_size(nullptr, example->getZExtValue());
      ucmo->update_ucmo_real_address(mo->getBaseExpr());
      bool result_1 = state.update_ucmo_constraints();
      if (!result_1) {
        terminateStateOnError(state, "update ucmo constraints failed",
                              StateTerminationType::Model);
        return;
      }

      // yuhao: set type for mo in alloc inst
      if (auto ai = dyn_cast<llvm::AllocaInst>(target->inst)) {
        //  std::string str;
        //  hy_dump(0, ai->print, str);
        //  hy_dump(0, ai->getAllocatedType()->print, str);
        add_mo_type(state, mo, ai->getAllocatedType());
      }

      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory) {
        os->initializeToZero();
      } else {
        os->initializeToRandom();
      }
      bindLocal(target, state, symbolic_address);

      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i = 0; i < count; i++)
          os->write(i, reallocFrom->read8(i));
        const MemoryObject *reallocObject = reallocFrom->getObject();
        state.deallocate(reallocObject);
        state.addressSpace.unbindObject(reallocObject);
      }
    }

    // XXX For now we just pick a size. Ideally we would support
    // symbolic sizes fully but even if we don't it would be better to
    // "smartly" pick a value, for example we could fork and pick the
    // min and max values and perhaps some intermediate (reasonable
    // value).
    //
    // It would also be nice to recognize the case when size has
    // exactly two values and just fork (but we need to get rid of
    // return argument first). This shows up in pcre when llvm
    // collapses the size expression with a select.

    // size = optimizer.optimizeExpr(size, true);

    // // yuhao:
    // ref<ConstantExpr> example = ConstantExpr::create(0, size->getWidth());
    // bool success =
    //     solver->getValue(state.constraints, size, example,
    //     state.queryMetaData);
    // // assert(success && "FIXME: Unhandled solver failure");

    // (void) success;

    // // Try and start with a small example.
    // Expr::Width W = example->getWidth();
    // while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
    //   ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
    //   bool res;
    //   bool success =
    //       solver->mayBeTrue(state.constraints, EqExpr::create(tmp, size),
    //       res,
    //                         state.queryMetaData);

    //   // yuhao:
    //   // assert(success && "FIXME: Unhandled solver failure");
    //   (void) success;
    //   if (!res)
    //     break;
    //   example = tmp;
    // }

    // StatePair fixedSize =
    //     fork(state, EqExpr::create(example, size), true, BranchType::Alloc);

    // if (fixedSize.second) {
    //   // Check for exactly two values

    //   // yuhao:
    //   ref<ConstantExpr> tmp = ConstantExpr::create(0, size->getWidth());
    //   bool success = solver->getValue(fixedSize.second->constraints, size,
    //   tmp,
    //                                   fixedSize.second->queryMetaData);
    //   // assert(success && "FIXME: Unhandled solver failure");

    //   (void) success;
    //   bool res;
    //   success = solver->mustBeTrue(fixedSize.second->constraints,
    //                                EqExpr::create(tmp, size), res,
    //                                fixedSize.second->queryMetaData);

    //   // yuhao:
    //   // assert(success && "FIXME: Unhandled solver failure");

    //   (void) success;
    //   if (res) {
    //     executeAlloc(*fixedSize.second, tmp, isLocal,
    //                  target, zeroMemory, reallocFrom);
    //   } else {
    //     // See if a *really* big value is possible. If so assume
    //     // malloc will fail for it, so lets fork and return 0.
    //     StatePair hugeSize =
    //         fork(*fixedSize.second,
    //              UltExpr::create(ConstantExpr::alloc(1U << 31, W), size),
    //              true, BranchType::Alloc);
    //     if (hugeSize.first) {
    //       klee_message("NOTE: found huge malloc, returning 0");
    //       bindLocal(target, *hugeSize.first,
    //                 ConstantExpr::alloc(0,
    //                 Context::get().getPointerWidth()));
    //     }

    //     if (hugeSize.second) {

    //       std::string Str;
    //       llvm::raw_string_ostream info(Str);
    //       ExprPPrinter::printOne(info, "  size expr", size);
    //       info << "  concretization : " << example << "\n";
    //       info << "  unbound example: " << tmp << "\n";
    //       terminateStateOnProgramError(*hugeSize.second,
    //                                    "concretized symbolic size",
    //                                    StateTerminationType::Model,
    //                                    info.str());
    //     }
    //   }
    // }

    // if (fixedSize.first) // can be zero when fork fails
    //   executeAlloc(*fixedSize.first, example, isLocal,
    //                target, zeroMemory, reallocFrom);
  }
}

void Executor::executeFree(ExecutionState &state, ref<Expr> address,
                           KInstruction *target) {

  // yuhao: debug
  int64_t debug = -1;
  std::string str;
  if (target != nullptr) {
    str = "executeFree: ";
    hy_add(debug, target->inst->print, str);
    hy_log(debug, str);
  }
  str = "executeFree: ";
  hy_add(debug, address->print, str);
  hy_log(debug, str);

  address = toUnique_ucmo(state, address);
  str = "executeFree: ";
  hy_add(debug, address->print, str);
  hy_log(debug, str);

  address = optimizer.optimizeExpr(address, true);
  StatePair zeroPointer =
      fork(state, Expr::createIsZero(address), true, BranchType::Free);
  if (zeroPointer.first) {
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0
    ExactResolutionList rl;
    resolveExact(*zeroPointer.second, address, rl, "free");

    for (Executor::ExactResolutionList::iterator it = rl.begin(), ie = rl.end();
         it != ie; ++it) {
      const MemoryObject *mo = it->first.first;
      if (mo->isLocal) {
        terminateStateOnProgramError(*it->second, "free of alloca",
                                     StateTerminationType::Free,
                                     getAddressInfo(*it->second, address));
      } else if (mo->isGlobal) {
        terminateStateOnProgramError(*it->second, "free of global",
                                     StateTerminationType::Free,
                                     getAddressInfo(*it->second, address));
      } else {
        it->second->deallocate(mo);
        it->second->addressSpace.unbindObject(mo);
        if (target)
          bindLocal(target, *it->second, Expr::createPointer(0));
      }
    }
  }
}

void Executor::resolveExact(ExecutionState &state, ref<Expr> p,
                            ExactResolutionList &results,
                            const std::string &name) {
  p = optimizer.optimizeExpr(p, true);
  // XXX we may want to be capping this?
  ResolutionList rl;
  state.addressSpace.resolve(state, solver.get(), p, rl);

  ExecutionState *unbound = &state;
  for (ResolutionList::iterator it = rl.begin(), ie = rl.end(); it != ie;
       ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());

    StatePair branches =
        fork(*unbound, inBounds, true, BranchType::ResolvePointer);

    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));

    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }

  if (unbound) {
    auto CE = dyn_cast<ConstantExpr>(p);
    if (MemoryManager::isDeterministic && CE) {
      using kdalloc::LocationInfo;
      auto ptr = reinterpret_cast<void *>(CE->getZExtValue());
      auto locinfo = unbound->heapAllocator.location_info(ptr, 1);
      if (locinfo == LocationInfo::LI_AllocatedOrQuarantined &&
          locinfo.getBaseAddress() == ptr && name == "free") {
        terminateStateOnProgramError(*unbound, "memory error: double free",
                                     StateTerminationType::Ptr,
                                     getAddressInfo(*unbound, p));
        return;
      }
    }
    terminateStateOnProgramError(
        *unbound, "memory error: invalid pointer: " + name,
        StateTerminationType::Ptr, getAddressInfo(*unbound, p));
  }
}

void Executor::executeMemoryOperation(ExecutionState &state, bool isWrite,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if read */,
                                      KInstruction *target /* undef if write */,
                                      int64_t operand /* operand of address */,
                                      uint64_t _size /* size of value */) {

  // yuhao: debug
  if (isWrite && value.isNull()) {
    std::string str;
    hy_log(3, "executeMemoryOperation: isWrite && value == nullptr");
    hy_log(2, "state id: " + std::to_string(state.getID()));
    if (target != nullptr) {
      hy_dump(2, target->inst->print, str);
    }
  }

  Expr::Width type = 0;
  if (_size) {
    type = _size;
  } else if (isWrite) {
    type = value->getWidth();
  } else if (target != nullptr) {
    type = getWidthForLLVMType(target->inst->getType());
  } else {
    hy_log(3, "executeMemoryOperation: no type provided");
  }
  unsigned bytes = Expr::getMinBytesForWidth(type);

  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = ConstraintManager::simplifyExpr(state.constraints, address);
    if (isWrite && !isa<ConstantExpr>(value))
      value = ConstraintManager::simplifyExpr(state.constraints, value);
  }

  address = optimizer.optimizeExpr(address, true);

  // yuhao: statistic about symbolic pointer
  if (!isa<ConstantExpr>(address)) {
    hy_log(2, "statistic: executeMemoryOperation: symbolic pointer");

    // XXX there is some query wasteage here. who cares?
    // we are on an error path (no resolution, multiple resolution, one
    // resolution with out of bounds)

    address = optimizer.optimizeExpr(address, true);
    ResolutionList rl;
    solver->setTimeout(coreSolverTimeout);
    state.addressSpace.resolve(state, solver.get(), address, rl, 0,
                               coreSolverTimeout);
    solver->setTimeout(time::Span());
    hy_log(2, "statistic: executeMemoryOperation: rl size: " + std::to_string(rl.size()));
  }

  // yuhao:
  // 1. figure out the base address if possible
  // 2. try to find memory object
  //    2.1. try to find ucmo, use the base address
  //    2.2. if not find, try to find other one mo by SMT solver
  //      2.2.1. use the base address if possible
  //    2.3. if not find, try to find many exisitng ucmo with type info
  //      this case may be not meaningful, we only care about existing ucmo
  //    2.4. if not find, for symbolic address, try to create new ucmo
  //      for constant address, possible bug

  // yuhao: if the address is symbolic, get the type of the memory object and
  // the base address
  int64_t debug = -1;
  std::string str;

  hy_log(debug, "executeMemoryOperation");
  hy_dump(debug, address->print, str);

  ref<Expr> base_address = address;
  llvm::Type *mo_type = nullptr;
  under_constrained_memory_object *ucmo = nullptr;
  under_constrained_memory_object *possible_smo = nullptr;

  // yuhao: try to find the existing uc memory object based on the base address
  // yuhao: if the base address is symbolic and it can be unique to constant,
  // we should find it and relocate it
  if (target != nullptr) {
    hy_dump(debug, target->inst->print, str);
    base_address = find_base_address(state, address, target, operand, &mo_type);
  }
  ucmo = find_ucmo_by_base_address(state, base_address);
  if (ucmo == nullptr || ucmo->is_created == false) {
    if (ucmo != nullptr) {
      possible_smo = ucmo;
    }
    ucmo = find_ucmo_flexible(state, base_address, address);
    if (ucmo == nullptr) {
      ucmo = possible_smo;
    }
  }

  if (ucmo != nullptr && ucmo->is_created == true) {
    // yuhao: check whether we have create memory object for it.
    // if so, we can directly use it and return.
    // yuhao: if the size of the memory object is not enough,
    // we need to create a new one and replace the old one
    hy_log(debug, "smo != nullptr && smo->is_created");

    if (ucmo->type != nullptr) {
      mo_type = ucmo->type;
      str = "smo mo_type: ";
      hy_add(debug, mo_type->print, str);
      hy_log(debug, str);
    }

    ObjectPair op;
    bool success;
    ref<Expr> real_smo_base_address = ucmo->real_address;
    str = "real_smo_base_address: ";
    hy_add(debug, real_smo_base_address->print, str);
    hy_log(debug, str);
    solver->setTimeout(coreSolverTimeout);
    if (!state.addressSpace.resolveOne(state, solver.get(),
                                       real_smo_base_address, op, success)) {
      real_smo_base_address =
          toConstant(state, real_smo_base_address, "resolveOne failure");
      success = state.addressSpace.resolveOne(
          cast<ConstantExpr>(real_smo_base_address), op);
    }
    solver->setTimeout(time::Span());

    if (success) {

      const MemoryObject *mo = op.first;

      if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
        real_smo_base_address =
            toConstant(state, real_smo_base_address, "max-sym-array-size");
      }

      ref<Expr> offset = SubExpr::create(address, real_smo_base_address);
      // yuhao: make the offset is unique value
      str = "old smo offset before toUnique_smo: ";
      hy_add_dump(debug, offset->print, str);
      offset = toUnique_ucmo(state, offset);
      str = "old smo offset: ";
      hy_add_dump(debug, offset->print, str);

      ref<Expr> check = mo->getBoundsCheckOffset(offset, bytes);
      check = optimizer.optimizeExpr(check, true);

      bool inBounds;
      solver->setTimeout(coreSolverTimeout);
      success = solver->mustBeTrue(*state.ucmo_constraints, check, inBounds,
                                   state.queryMetaData);
      solver->setTimeout(time::Span());
      if (!success) {
        state.pc = state.prevPC;
        terminateStateOnSolverError(state, "Query timed out (bounds check).");
        return;
      }

      if (inBounds) {
        const ObjectState *os = op.second;
        if (isWrite) {
          if (os->readOnly) {
            terminateStateOnError(state, "memory error: object read only",
                                  StateTerminationType::ReadOnly);
          } else {
            ObjectState *wos = state.addressSpace.getWriteable(mo, os);
            wos->write(offset, value);
          }
        } else {
          ref<Expr> result = os->read(offset, type);

          if (interpreterOpts.MakeConcreteSymbolic)
            result = replaceReadWithSymbolic(state, result);

          bindLocal(target, state, result);
        }

        return;
      } else {
        // yuhao: if the offset is not in bound, we need to resize the smo
        // consider the offset is bigger or negative
        hy_log(debug, "smo is not inbound, resize smo");

        // yuhao: record old os
        const ObjectState *old_os = op.second;

        // yuhao: get the new size and new base address
        ref<Expr> new_base_address = ucmo->base_address;
        uint64_t new_offset = 0;
        uint64_t new_size = ucmo->size;
        uint64_t ucmo_addr_int =
            cast<klee::ConstantExpr>(ucmo->real_address)->getZExtValue();
        uint64_t start_addr_int = ucmo_addr_int;
        uint64_t end_addr_int = ucmo_addr_int + ucmo->size;

        // yuhao: for negative offset
        // update the start and new base address
        ref<Expr> unique_base_addr = toUnique_ucmo(state, base_address);
        if (isa<ConstantExpr>(unique_base_addr)) {
          uint64_t unique_base_addr_int =
              cast<klee::ConstantExpr>(unique_base_addr)->getZExtValue();
          if (unique_base_addr_int < start_addr_int) {
            new_offset = start_addr_int - unique_base_addr_int;
            start_addr_int = unique_base_addr_int;
            new_base_address = base_address;
          }

          // yuhao: check the real size of the type
          if (mo_type != nullptr) {
            // yuhao: get the real size of the type (in bytes)
            uint64_t type_size =
                Expr::getMinBytesForWidth(getWidthForLLVMType(mo_type));
            if (unique_base_addr_int + type_size > end_addr_int) {
              end_addr_int = unique_base_addr_int + type_size;
            }
          }
        }

        // yuhao: for bigger offset
        ref<Expr> unique_addr = toUnique_ucmo(state, address);
        if (isa<ConstantExpr>(unique_addr)) {
          uint64_t unique_addr_int =
              cast<klee::ConstantExpr>(unique_addr)->getZExtValue();
          if ((unique_addr_int + bytes) > end_addr_int) {
            end_addr_int = unique_addr_int + bytes;
          }
        }

        // yuhao: update the new size based on the new start and end
        if (end_addr_int - start_addr_int > new_size) {
          new_size = end_addr_int - start_addr_int;
        }

        hy_log(debug, "bytes: " + std::to_string(bytes));
        str = "new_base_address: ";
        hy_add_dump(debug, new_base_address->print, str);
        hy_log(debug, "size: " + std::to_string(new_size));

        // yuhao: create resize memory object
        MemoryObject *resize_mo = create_ucmo(
            state, get_uc_name(get_name(base_address)), target->inst, new_size);

        str = "create resize smo base_address: ";
        hy_add_dump(-1, base_address->print, str);
        str = "create resize smo old mo address: ";
        hy_add_dump(-1, mo->getBaseExpr()->print, str);
        str = "create resize smo new resize mo address: ";
        hy_add_dump(-1, resize_mo->getBaseExpr()->print, str);

        // yuhao: update the ucmo
        // update the symbolic address map: old base address -> new base address
        state.under_constrained_memory_objects.erase(ucmo->base_address);
        state.under_constrained_memory_objects[new_base_address] = ucmo;
        ucmo->base_address = new_base_address;

        state.symbolic_address_map[ucmo->base_address] = new_base_address;
        ucmo->update_ucmo_size(nullptr, new_size);
        ref<Expr> resize_base_address = resize_mo->getBaseExpr();
        ucmo->update_ucmo_real_address(resize_base_address);
        
        bool result_1 = state.update_ucmo_constraints();
        if (!result_1) {
          terminateStateOnError(state, "update ucmo constraints failed",
                                StateTerminationType::Model);
          return;
        }

        // yuhao: get the mo and os based on the new real address
        ObjectPair new_op;
        state.addressSpace.resolveOne(
            state, solver.get(), resize_base_address, new_op, success);

        // yuhao: initialize the resize object from the old one
        const ObjectState *resize_os = new_op.second;
        ObjectState *wresize_os =
            state.addressSpace.getWriteable(resize_mo, resize_os);
        wresize_os->copy_from(old_os, new_offset);

        // yuhao:: unbind the old object
        // state.addressSpace.unbindObject(old_os->getObject());

        // yuhao: update the offset
        offset = SubExpr::create(address, ucmo->real_address);
        str = "update smo offset before toUnique_smo: ";
        hy_add_dump(debug, offset->print, str);
        offset = toUnique_ucmo(state, offset);
        str = "update smo offset: ";
        hy_add_dump(debug, offset->print, str);

        // yuhao: read/write the new object
        if (isWrite) {
          if (resize_os->readOnly) {
            terminateStateOnError(state, "memory error: object read only",
                                  StateTerminationType::ReadOnly);
          } else {
            ObjectState *wresize_os =
                state.addressSpace.getWriteable(resize_mo, resize_os);
            wresize_os->write(offset, value);
          }
        } else {
          ref<Expr> result = resize_os->read(offset, type);

          if (interpreterOpts.MakeConcreteSymbolic)
            result = replaceReadWithSymbolic(state, result);

          bindLocal(target, state, result);
        }
        return;
      }
    } else {

      terminateStateOnError(
          state, "smo != nullptr && smo->is_created, but not success find mo",
          StateTerminationType::ReadOnly);
      hy_log(3, "smo != nullptr && smo->is_created, but not success find mo\n");
      return;
    }
  }

  if (ucmo == nullptr) {
    hy_log(debug, "smo == nullptr, not find smo");
    goto end_find_created_smo;
  }

  if (ucmo->is_created == false) {
    hy_log(debug, "smo->is_created == false");
    goto end_find_created_smo;
  }

end_find_created_smo:

  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success;
  solver->setTimeout(coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver.get(), base_address, op,
                                     success)) {
    base_address = toConstant(state, base_address, "resolveOne failure");
    success =
        state.addressSpace.resolveOne(cast<ConstantExpr>(base_address), op);
  }
  solver->setTimeout(time::Span());

  if (success) {

    // yuhao: debug
    hy_log(debug, "find one success");

    const MemoryObject *mo = op.first;

    if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
      address = toConstant(state, address, "max-sym-array-size");
    }

    ref<Expr> offset = mo->getOffsetExpr(address);
    ref<Expr> check = mo->getBoundsCheckOffset(offset, bytes);

    // yuhao: debug
    str = "one success offset: ";
    hy_add_dump(debug, offset->print, str);

    check = optimizer.optimizeExpr(check, true);

    bool inBounds;
    solver->setTimeout(coreSolverTimeout);
    // yuhao:
    bool success = solver->mustBeTrue(*state.ucmo_constraints, check, inBounds,
                                      state.queryMetaData);
    solver->setTimeout(time::Span());
    if (!success) {
      state.pc = state.prevPC;
      terminateStateOnSolverError(state, "Query timed out (bounds check).");
      return;
    }

    // yuhao: debug
    str = "one success check: ";
    hy_add_dump(debug, check->print, str);

    if (inBounds) {

      // yuhao: debug
      hy_log(debug, "find one inBounds");

      const ObjectState *os = op.second;
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnProgramError(state, "memory error: object read only",
                                       StateTerminationType::ReadOnly);
        } else {
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          wos->write(offset, value);
        }
      } else {
        ref<Expr> result = os->read(offset, type);

        if (interpreterOpts.MakeConcreteSymbolic)
          result = replaceReadWithSymbolic(state, result);

        bindLocal(target, state, result);
      }

      return;
    }
  } else {
    // yuhao: debug
    hy_log(debug, "find one not success");
  }

  // yuhao: only check whether the symbolic address could be resolved to any
  // existing uc simbolic memory object based on constrains and type info. so
  // skip this
  ExecutionState *unbound = &state;
  bool incomplete = false;

  // // we are on an error path (no resolution, multiple resolution, one
  // // resolution with out of bounds)

  // address = optimizer.optimizeExpr(address, true);
  // ResolutionList rl;
  // solver->setTimeout(coreSolverTimeout);
  // bool incomplete = state.addressSpace.resolve(state, solver.get(), address,
  // rl,
  //                                              0, coreSolverTimeout);
  // solver->setTimeout(time::Span());

  // // XXX there is some query wasteage here. who cares?
  // ExecutionState *unbound = &state;

  // // yuhao:
  // hy_log(debug, "for (ResolutionList::iterator i = rl.begin(), ie =
  // rl.end();)"); hy_log(debug, "rl size: " + std::to_string(rl.size()));

  // for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i)
  // {
  //   const MemoryObject *mo = i->first;
  //   const ObjectState *os = i->second;
  //   ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

  //   // yuhao: inBounds2 make sure the mo include the base_address
  //   ref<Expr> inBounds2 = UgeExpr::create(base_address, mo->getBaseExpr());
  //   ref<Expr> inBounds3 = AndExpr::create(inBounds, inBounds2);
  //   StatePair branches = fork(*unbound, inBounds3, true, BranchType::MemOp);

  //   // yuhao: debug
  //   hy_log(debug, "fork(*unbound, inBounds3, true, BranchType::MemOp);");
  //   str = "";
  //   mo->getAllocInfo(str);
  //   hy_log(debug, str);
  //   hy_dump(debug, inBounds3->print, str);

  //   ExecutionState *bound = branches.first;

  //   // bound can be 0 on failure or overlapped
  //   if (bound) {
  //     if (isWrite) {
  //       if (os->readOnly) {
  //         terminateStateOnProgramError(*bound, "memory error: object read
  //         only",
  //                                      StateTerminationType::ReadOnly);
  //       } else {
  //         ObjectState *wos = bound->addressSpace.getWriteable(mo, os);
  //         wos->write(mo->getOffsetExpr(address), value);
  //       }
  //     } else {
  //       ref<Expr> result = os->read(mo->getOffsetExpr(address), type);
  //       bindLocal(target, *bound, result);
  //     }
  //   }

  //   unbound = branches.second;
  //   if (!unbound)
  //     break;
  // }

  // XXX should we distinguish out of bounds and overlapped cases?
  if (unbound) {
    if (incomplete) {
      terminateStateOnSolverError(*unbound, "Query timed out (resolve).");
    } else {
      if (auto CE = dyn_cast<ConstantExpr>(address)) {
        std::uintptr_t ptrval = CE->getZExtValue();
        auto ptr = reinterpret_cast<void *>(ptrval);
        if (ptrval < MemoryManager::pageSize) {
          terminateStateOnProgramError(
              *unbound, "memory error: null page access",
              StateTerminationType::Ptr, getAddressInfo(*unbound, address));
          return;
        } else if (MemoryManager::isDeterministic) {
          using kdalloc::LocationInfo;
          auto li = unbound->heapAllocator.location_info(ptr, bytes);
          if (li == LocationInfo::LI_AllocatedOrQuarantined) {
            // In case there is no size mismatch (checked by resolving for base
            // address), the object is quarantined.
            auto base = reinterpret_cast<std::uintptr_t>(li.getBaseAddress());
            auto baseExpr = Expr::createPointer(base);
            ObjectPair op;
            if (!unbound->addressSpace.resolveOne(baseExpr, op)) {
              terminateStateOnProgramError(
                  *unbound, "memory error: use after free",
                  StateTerminationType::Ptr, getAddressInfo(*unbound, address));
              return;
            }
          }
        }

        // yuhao: todo handle this case in the future
        terminateStateOnProgramError(
            *unbound, "memory error: out of bound pointer",
            StateTerminationType::Ptr, getAddressInfo(*unbound, address));
      } else {
        // yuhao: create new memory object for symbolic
        // if we can find the structure type, create new memory object for the
        // whole structure otherwise create a single memory object for the
        // pointer
        
        hy_log(2, "statistic: executeMemoryOperation: create new ucmo");
        if (ucmo == nullptr) {
          ucmo = create_ucmo_by_base_address(*unbound, base_address);
        }
        MemoryObject *mo = nullptr;
        if (ucmo->is_created) {
          hy_log(3, "smo->is_created: impossible situation");
          terminateStateOnProgramError(
              *unbound, "smo->is_created: impossible situation",
              StateTerminationType::Ptr, getAddressInfo(*unbound, address));
          return;
        }

        if (mo_type == nullptr) {
          if (isWrite) {
            mo_type = target->inst->getOperand(0)->getType();
          } else {
            mo_type = target->inst->getType();
          }
        }
        ucmo->update_ucmo_size(mo_type,
                               kmodule->targetData->getTypeStoreSize(mo_type));
        mo = create_ucmo(*unbound, get_uc_name(get_name(base_address)),
                         target->inst, ucmo->size, mo_type);

        str = "create new smo type: ";
        hy_add_dump(-1, mo_type->print, str);
        str = "create new smo base_address: ";
        hy_add_dump(-1, base_address->print, str);
        str = "create new smo mo address: ";
        hy_add_dump(-1, mo->getBaseExpr()->print, str);

        ucmo->update_ucmo_real_address(mo->getBaseExpr());

        hy_log(debug, "create smo constraints");
        for (auto c : *unbound->ucmo_constraints) {
          hy_dump(debug, c->print, str);
        }

        ref<Expr> base_address = ucmo->base_address;
        ref<Expr> real_address = ucmo->real_address;
        ref<Expr> _constraint = EqExpr::create(base_address, real_address);
        str = "unbound add_ucmo_constraints2: ";
        hy_add_dump(debug, _constraint->print, str);
        bool isTrue = false;
        solver->setTimeout(coreSolverTimeout);
        bool success = solver->mayBeTrue(*state.ucmo_constraints, _constraint,
                                         isTrue, state.queryMetaData);
        solver->setTimeout(time::Span());
        if (success && isTrue) {
          unbound->add_ucmo_constraints(ucmo);
        } else {
          terminateStateOnError(*unbound, "unbound create smo error",
                                StateTerminationType::InvalidLoad);
          return;
        }

        ref<Expr> offset = SubExpr::create(address, base_address);
        // yuhao: make the offset is unique value
        str = "new smo offset before toUnique_smo: ";
        hy_add_dump(debug, offset->print, str);
        offset = toUnique_ucmo(*unbound, offset);
        str = "new smo offset: ";
        hy_add_dump(debug, offset->print, str);

        // yuhao: todo add constraint for the offset
        // however, I think it is impossible to get a symbolic offset
        // so I do not add the constraint now

        // yuhao: when create new smo, maintain linked list prev and next
        maintain_linked_list(state, target, isWrite, mo, base_address);

        // yuhao: write or read the value
        const ObjectState *os = unbound->addressSpace.findObject(mo);
        if (isa<ConstantExpr>(offset)) {
          uint64_t offset_int =
              cast<klee::ConstantExpr>(offset)->getZExtValue();
          if (offset_int + bytes > mo->size) {
            terminateStateOnError(*unbound,
                                  "memory error: offset_int + bytes > mo->size",
                                  StateTerminationType::Ptr);
            return;
          }
        }

        if (isWrite) {
          if (os->readOnly) {
            terminateStateOnError(*unbound, "memory error: object read only",
                                  StateTerminationType::ReadOnly);
          } else {
            ObjectState *wos = unbound->addressSpace.getWriteable(mo, os);
            wos->write(offset, value);
          }
        } else {
          ref<Expr> result = os->read(offset, type);
          bindLocal(target, *unbound, result);
        }
      }
    }
  }
}

void Executor::executeMakeSymbolic(ExecutionState &state,
                                   const MemoryObject *mo,
                                   const std::string &name) {
  // Create a new object state for the memory object (instead of a copy).
  if (!replayKTest) {
    // Find a unique name for this array.  First try the original name,
    // or if that fails try adding a unique identifier.
    unsigned id = 0;
    std::string uniqueName = name;
    while (!state.arrayNames.insert(uniqueName).second) {
      uniqueName = name + "_" + llvm::utostr(++id);
    }
    const Array *array = arrayCache.CreateArray(uniqueName, mo->size);
    bindObjectInState(state, mo, false, array);
    state.addSymbolic(mo, array);

    std::map<ExecutionState *, std::vector<SeedInfo>>::iterator it =
        seedMap.find(&state);
    if (it != seedMap.end()) { // In seed mode we need to add this as a
                               // binding.
      for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
                                           siie = it->second.end();
           siit != siie; ++siit) {
        SeedInfo &si = *siit;
        KTestObject *obj = si.getNextInput(mo, NamedSeedMatching);

        if (!obj) {
          if (ZeroSeedExtension) {
            std::vector<unsigned char> &values = si.assignment.bindings[array];
            values = std::vector<unsigned char>(mo->size, '\0');
          } else if (!AllowSeedExtension) {
            terminateStateOnUserError(state,
                                      "ran out of inputs during seeding");
            break;
          }
        } else {
          if (obj->numBytes != mo->size &&
              ((!(AllowSeedExtension || ZeroSeedExtension) &&
                obj->numBytes < mo->size) ||
               (!AllowSeedTruncation && obj->numBytes > mo->size))) {
            std::stringstream msg;
            msg << "replace size mismatch: " << mo->name << "[" << mo->size
                << "]"
                << " vs " << obj->name << "[" << obj->numBytes << "]"
                << " in test\n";

            terminateStateOnUserError(state, msg.str());
            break;
          } else {
            std::vector<unsigned char> &values = si.assignment.bindings[array];
            values.insert(values.begin(), obj->bytes,
                          obj->bytes + std::min(obj->numBytes, mo->size));
            if (ZeroSeedExtension) {
              for (unsigned i = obj->numBytes; i < mo->size; ++i)
                values.push_back('\0');
            }
          }
        }
      }
    }
  } else {
    ObjectState *os = bindObjectInState(state, mo, false);
    if (replayPosition >= replayKTest->numObjects) {
      terminateStateOnUserError(state, "replay count mismatch");
    } else {
      KTestObject *obj = &replayKTest->objects[replayPosition++];
      if (obj->numBytes != mo->size) {
        terminateStateOnUserError(state, "replay size mismatch");
      } else {
        for (unsigned i = 0; i < mo->size; i++)
          os->write8(i, obj->bytes[i]);
      }
    }
  }
}

// yuhao:
void Executor::prepare_for_kernel() { spec_config.read_config(); }

// yuhao:
void Executor::runFunctionAsMain(Function *f, int argc, char **argv,
                                 char **envp) {
  // prepare_for_kernel();
  
  // yuhao: for type based call graph
  multi_layer_type_analysis();
  Module *m = kmodule->module.get();
  for (Function &f : *m) {
    if (f.hasAddressTaken()) {
      auto *ft = f.getFunctionType();
      if (this->map_function_type.find(ft) == this->map_function_type.end()) {
        auto set_function = new std::set<llvm::Function *>;
        set_function->insert(&f);
        this->map_function_type[ft] = set_function;
      } else {
        this->map_function_type[ft]->insert(&f);
      }
    }
  }

  // yuhao: initialize an empty state at the beginning
  auto *state = new ExecutionState();
  states_before_running.push_back(state);
  initializeGlobals(*state);
  bindModuleConstants();

  // yuhao: main loop to run all entry functions on all states
  entry_functions.push(f);
  update_entry_functions();
  while (!entry_functions.empty()) {
    auto func = entry_functions.front();
    entry_functions.pop();
    hy_log(-1, "execute function: " + func->getName().str() +
                   " with state size: " +
                   std::to_string(states_before_running.size()));
    for (auto &&state : states_before_running) {
      hy_log(1, "execute function: " + func->getName().str() +
                    " at state: " + std::to_string(state->getID()));
      runEntryFunction(state, func, argc, argv, envp);
      hy_log(1, "finish function: " + func->getName().str());
    }

    states_before_running.clear();
    states_before_running.swap(states_after_running);

    update_entry_functions();
  }

  // hack to clear memory objects
  memory = nullptr;

  globalObjects.clear();
  globalAddresses.clear();

  if (statsTracker)
    statsTracker->done();
}

/***/

void Executor::runEntryFunction(ExecutionState *state, Function *f, int argc,
                                char **argv, char **envp) {
  std::vector<ref<Expr>> arguments;

  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);

  MemoryObject *argvMO = 0;

  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?

  int envc;
  for (envc = 0; envp[envc]; ++envc)
    ;

  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  // yuhao: create symbolic expr for arguments when entry function is not main
  if (f->getName().str() == "main") {
    if (ai != ae) {
      arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));
      if (++ai != ae) {
        Instruction *first = &*(f->begin()->begin());
        argvMO = memory->allocate((argc + 1 + envc + 1 + 1) * NumPtrBytes,
                                  /*isLocal=*/false, /*isGlobal=*/true,
                                  /*state=*/nullptr, /*allocSite=*/first,
                                  /*alignment=*/8);

        if (!argvMO)
          klee_error("Could not allocate memory for function arguments");

        arguments.push_back(argvMO->getBaseExpr());

        if (++ai != ae) {
          uint64_t envp_start = argvMO->address + (argc + 1) * NumPtrBytes;
          arguments.push_back(Expr::createPointer(envp_start));

          if (++ai != ae)
            klee_error("invalid main function (expect 0-3 arguments)");
        }
      }
    }
  } else {
    // yuhao: create symbolic expr for arguments
    for (uint64_t i = 0; ai != ae; ai++, i++) {
      bool is_input = true;
      if (i < this->spec_config.arguments_index) {
        is_input = false;
      } else if (this->spec_config.arguments_num > 0 &&
                 (i >= this->spec_config.arguments_index +
                           this->spec_config.arguments_num)) {
        is_input = false;
      }

      ref<Expr> expr = create_symbolic_arg(*state, f, ai->getType(), is_input);
      arguments.push_back(expr);
      // yuhao: record user arguments
      user_arguments.push_back(expr);
      user_arguments_type.push_back(ai->getType());
    }
  }

  // yuhao:
  // ExecutionState *state =
  //     new ExecutionState(kmodule->functionMap[f], memory.get());
  state->set_function(kmodule->functionMap[f]);

  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();

  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
    bindArgument(kf, i, *state, arguments[i]);

  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*state, argvMO, false);

    for (int i = 0; i < argc + 1 + envc + 1 + 1; i++) {
      if (i == argc || i >= argc + 1 + envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i < argc ? argv[i] : envp[i - (argc + 1)];
        int j, len = strlen(s);

        MemoryObject *arg =
            memory->allocate(len + 1, /*isLocal=*/false, /*isGlobal=*/true,
                             state, /*allocSite=*/state->pc->inst,
                             /*alignment=*/8);
        if (!arg)
          klee_error("Could not allocate memory for function arguments");
        ObjectState *os = bindObjectInState(*state, arg, false);
        for (j = 0; j < len + 1; j++)
          os->write8(j, s[j]);

        // Write pointer to newly allocated and initialised argv/envp c-string
        argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
      }
    }
  }

  // yuhao:
  // initializeGlobals(*state);

  processTree = std::make_unique<PTree>(state);
  run(*state);
  processTree = nullptr;

  // yuhao:
  // // hack to clear memory objects
  // memory = nullptr;

  // globalObjects.clear();
  // globalAddresses.clear();

  // if (statsTracker)
  //   statsTracker->done();
}

unsigned Executor::getPathStreamID(const ExecutionState &state) {
  assert(pathWriter);
  return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
  assert(symPathWriter);
  return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res,
                                Interpreter::LogType logFormat) {

  switch (logFormat) {
  case STP: {
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    char *log = solver->getConstraintLog(query);
    res = std::string(log);
    free(log);
  } break;

  case KQUERY: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprPPrinter::printConstraints(info, state.constraints);
    res = info.str();
  } break;

  case SMTLIB2: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprSMTLIBPrinter printer;
    printer.setOutput(info);
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    printer.setQuery(query);
    printer.generateOutput();
    res = info.str();
  } break;

  default:
    klee_warning("Executor::getConstraintLog() : Log format not supported!");
  }
}

bool Executor::getSymbolicSolution(
    const ExecutionState &state,
    std::vector<std::pair<std::string, std::vector<unsigned char>>> &res) {
  solver->setTimeout(coreSolverTimeout);

  ConstraintSet extendedConstraints(state.constraints);
  ConstraintManager cm(extendedConstraints);

  // Go through each byte in every test case and attempt to restrict
  // it to the constraints contained in cexPreferences.  (Note:
  // usually this means trying to make it an ASCII character (0-127)
  // and therefore human readable. It is also possible to customize
  // the preferred constraints.  See test/Features/PreferCex.c for
  // an example) While this process can be very expensive, it can
  // also make understanding individual test cases much easier.
  for (auto &pi : state.cexPreferences) {
    bool mustBeTrue;
    // Attempt to bound byte to constraints held in cexPreferences
    bool success =
        solver->mustBeTrue(extendedConstraints, Expr::createIsZero(pi),
                           mustBeTrue, state.queryMetaData);
    // If it isn't possible to add the condition without making the entire list
    // UNSAT, then just continue to the next condition
    if (!success)
      break;
    // If the particular constraint operated on in this iteration through
    // the loop isn't implied then add it to the list of constraints.
    if (!mustBeTrue)
      cm.addConstraint(pi);
  }

  std::vector<std::vector<unsigned char>> values;
  std::vector<const Array *> objects;
  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    objects.push_back(state.symbolics[i].second);
  bool success = solver->getInitialValues(extendedConstraints, objects, values,
                                          state.queryMetaData);
  solver->setTimeout(time::Span());
  if (!success) {
    klee_warning("unable to compute initial values (invalid constraints?)!");
    // yuhao:
    // ExprPPrinter::printQuery(llvm::errs(), state.constraints,
    //                          ConstantExpr::alloc(0, Expr::Bool));
    return false;
  }

  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    res.push_back(std::make_pair(state.symbolics[i].first->name, values[i]));
  return true;
}

void Executor::getCoveredLines(
    const ExecutionState &state,
    std::map<const std::string *, std::set<unsigned>> &res) {
  res = state.coveredLines;
}

void Executor::doImpliedValueConcretization(ExecutionState &state, ref<Expr> e,
                                            ref<ConstantExpr> value) {
  abort(); // FIXME: Broken until we sort out how to do the write back.

  if (DebugCheckForImpliedValues)
    ImpliedValue::checkForImpliedValues(solver->solver.get(), e, value);

  ImpliedValueList results;
  ImpliedValue::getImpliedValues(e, value, results);
  for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
       it != ie; ++it) {
    ReadExpr *re = it->first.get();

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
      // FIXME: This is the sole remaining usage of the Array object
      // variable. Kill me.
      const MemoryObject *mo = 0; // re->updates.root->object;
      const ObjectState *os = state.addressSpace.findObject(mo);

      if (!os) {
        // object has been free'd, no need to concretize (although as
        // in other cases we would like to concretize the outstanding
        // reads, but we have no facility for that yet)
      } else {
        assert(!os->readOnly &&
               "not possible? read only object with static read?");
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        wos->write(CE, it->second);
      }
    }
  }
}

Expr::Width Executor::getWidthForLLVMType(llvm::Type *type) const {
  return kmodule->targetData->getTypeSizeInBits(type);
}

size_t Executor::getAllocationAlignment(const llvm::Value *allocSite) const {
  // FIXME: 8 was the previous default. We shouldn't hard code this
  // and should fetch the default from elsewhere.
  const size_t forcedAlignment = 8;
  size_t alignment = 0;
  llvm::Type *type = NULL;
  std::string allocationSiteName(allocSite->getName().str());
  if (const GlobalObject *GO = dyn_cast<GlobalObject>(allocSite)) {
    alignment = GO->getAlignment();
    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(GO)) {
      // All GlobalVariables's have pointer type
      assert(globalVar->getType()->isPointerTy() &&
             "globalVar's type is not a pointer");
      type = globalVar->getValueType();
    } else {
      type = GO->getType();
    }
  } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(allocSite)) {
    alignment = AI->getAlignment();
    type = AI->getAllocatedType();
  } else if (isa<InvokeInst>(allocSite) || isa<CallInst>(allocSite)) {
    // FIXME: Model the semantics of the call to use the right alignment
    const CallBase &cb = cast<CallBase>(*allocSite);
    llvm::Function *fn =
        klee::getDirectCallTarget(cb, /*moduleIsFullyLinked=*/true);
    if (fn)
      allocationSiteName = fn->getName().str();

    klee_warning_once(fn != NULL ? fn : allocSite,
                      "Alignment of memory from call \"%s\" is not "
                      "modelled. Using alignment of %zu.",
                      allocationSiteName.c_str(), forcedAlignment);
    alignment = forcedAlignment;
  } else {
    llvm_unreachable("Unhandled allocation site");
  }

  if (alignment == 0) {
    assert(type != NULL);
    // No specified alignment. Get the alignment for the type.
    if (type->isSized()) {
      alignment = kmodule->targetData->getPrefTypeAlignment(type);
    } else {
      klee_warning_once(allocSite,
                        "Cannot determine memory alignment for "
                        "\"%s\". Using alignment of %zu.",
                        allocationSiteName.c_str(), forcedAlignment);
      alignment = forcedAlignment;
    }
  }

  // Currently we require alignment be a power of 2
  if (!bits64::isPowerOfTwo(alignment)) {
    klee_warning_once(allocSite,
                      "Alignment of %zu requested for %s but this "
                      "not supported. Using alignment of %zu",
                      alignment, allocSite->getName().str().c_str(),
                      forcedAlignment);
    alignment = forcedAlignment;
  }
  assert(bits64::isPowerOfTwo(alignment) &&
         "Returned alignment must be a power of two");
  return alignment;
}

void Executor::prepareForEarlyExit() {
  if (statsTracker) {
    // Make sure stats get flushed out
    statsTracker->done();
  }
}

/// Returns the errno location in memory
int *Executor::getErrnoLocation(const ExecutionState &state) const {
#if !defined(__APPLE__) && !defined(__FreeBSD__)
  /* From /usr/include/errno.h: it [errno] is a per-thread variable. */
  return __errno_location();
#else
  return __error();
#endif
}

void Executor::dumpPTree() {
  if (!::dumpPTree)
    return;

  char name[32];
  snprintf(name, sizeof(name), "ptree%08d.dot", (int)stats::instructions);
  auto os = interpreterHandler->openOutputFile(name);
  if (os) {
    processTree->dump(*os);
  }

  ::dumpPTree = 0;
}

void Executor::dumpStates() {
  if (!::dumpStates)
    return;

  auto os = interpreterHandler->openOutputFile("states.txt");

  if (os) {
    for (ExecutionState *es : states) {
      *os << "(" << es << ",";
      *os << "[";
      auto next = es->stack.begin();
      ++next;
      for (auto sfIt = es->stack.begin(), sf_ie = es->stack.end();
           sfIt != sf_ie; ++sfIt) {
        *os << "('" << sfIt->kf->function->getName().str() << "',";
        if (next == es->stack.end()) {
          *os << es->prevPC->info->line << "), ";
        } else {
          *os << next->caller->info->line << "), ";
          ++next;
        }
      }
      *os << "], ";

      StackFrame &sf = es->stack.back();
      uint64_t md2u =
          computeMinDistToUncovered(es->pc, sf.minDistToUncoveredOnReturn);
      uint64_t icnt = theStatisticManager->getIndexedValue(stats::instructions,
                                                           es->pc->info->id);
      uint64_t cpicnt =
          sf.callPathNode->statistics.getValue(stats::instructions);

      *os << "{";
      *os << "'depth' : " << es->depth << ", ";
      *os << "'queryCost' : " << es->queryMetaData.queryCost << ", ";
      *os << "'coveredNew' : " << es->coveredNew << ", ";
      *os << "'instsSinceCovNew' : " << es->instsSinceCovNew << ", ";
      *os << "'md2u' : " << md2u << ", ";
      *os << "'icnt' : " << icnt << ", ";
      *os << "'CPicnt' : " << cpicnt << ", ";
      *os << "}";
      *os << ")\n";
    }
  }

  ::dumpStates = 0;
}

///

Interpreter *Interpreter::create(LLVMContext &ctx,
                                 const InterpreterOptions &opts,
                                 InterpreterHandler *ih) {
  return new Executor(ctx, opts, ih);
}

// yuhao:
ref<Expr> Executor::manual_make_symbolic(ExecutionState &state,
                                         const std::string &symbolic_name,
                                         const llvm::Value *allocSite,
                                         uint64_t type_store_size,
                                         uint64_t type_load_size,
                                         llvm::Type *ty) {
  //  hy_log(-1, "make symbolic: " + symbolic_name);
  MemoryObject *mo =
      create_ucmo(state, symbolic_name, allocSite, type_store_size, ty);
  const ObjectState *os = state.addressSpace.findObject(mo);
  if (os == nullptr) {
    klee_error("can not find mo");
    return nullptr;
  }
  ref<Expr> symbolic =
      os->read(ConstantExpr::create(0, Expr::Int32), type_load_size);
  return symbolic;
}

// yuhao:
ref<Expr> Executor::create_symbolic_arg(ExecutionState &state,
                                        const llvm::Value *allocSite,
                                        llvm::Type *ty, bool is_input) {
  ref<Expr> expr;
  if (ty->isSized()) {
    std::string name;
    if (is_input) {
      name = get_symbolic_name(input_name, input_count);
    } else {
      name = get_symbolic_name(global_name, global_count);
    }
    uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
    Expr::Width width = getWidthForLLVMType(ty);
    expr = manual_make_symbolic(state, name, allocSite, size, width, ty);
  } else {
    klee_error("function arguments do not have size");
  }
  return expr;
}

// yuhao:
uint64_t Executor::specification_handle(ExecutionState &state) {

  std::string str;
  int64_t debug = 1;
  uint64_t ret = 0;

  hy::Specification *spec = new hy::Specification();
  spec->id = state.getID();

  for (uint64_t i = 0; i < user_arguments.size(); i++) {

    // yuhao: skip the some argument
    if (i < this->spec_config.arguments_index) {
      continue;
    } else if (this->spec_config.arguments_num > 0 &&
               i >= this->spec_config.arguments_index +
                        this->spec_config.arguments_num) {
      continue;
    }

    ref<Expr> arg = user_arguments[i];
    llvm::Type *ty = user_arguments_type[i];
    hy_log(debug, "output_arguments: state: " + std::to_string(state.id) +
                      " arg: " + std::to_string(i));
    hy_dump(debug, arg->print, str);

    hy::Type *results = specification_handle_type(state, ty, arg);

    spec->add(results);
  }

  ret = spec_manager.add_spec(state.getID(), spec);
  return ret;
}

// yuhao:
hy::Type *Executor::specification_handle_type(ExecutionState &state,
                                              llvm::Type *ty, ref<Expr> expr,
                                              const ObjectState *os,
                                              uint64_t offset) {
  std::string str;
  int64_t debug = -1;

  hy_log(debug, "specification_handle_type: type: ");
  hy_dump(debug, ty->print, str);
  hy_log(debug, "offset: " + std::to_string(offset));

  hy::Type *result = nullptr;

  switch (ty->getTypeID()) {
  case llvm::Type::HalfTyID:
  case llvm::Type::BFloatTyID:
  case llvm::Type::FloatTyID:
  case llvm::Type::DoubleTyID:
  case llvm::Type::X86_FP80TyID:
  case llvm::Type::FP128TyID:
  case llvm::Type::PPC_FP128TyID:
  case llvm::Type::VoidTyID:
  case llvm::Type::LabelTyID:
  case llvm::Type::MetadataTyID:
  case llvm::Type::X86_MMXTyID:
  case llvm::Type::X86_AMXTyID:
  case llvm::Type::TokenTyID:
  case llvm::Type::FunctionTyID:
  case llvm::Type::FixedVectorTyID:
  case llvm::Type::ScalableVectorTyID:
    hy_log(2, "specification_handle: unsupported type: " +
                  std::to_string(ty->getTypeID()));
    break;
  case llvm::Type::IntegerTyID:
  case llvm::Type::PointerTyID: {
    // yuhao: handle the case that it is a integer or possible pointer

    if (os != nullptr) {
      expr = os->read(offset, getWidthForLLVMType(ty));
    }

    result = specification_handle_pointer(state, ty, expr);
    break;
  }
  case llvm::Type::ArrayTyID: {
    // yuhao: handle the case that it is an array

    hy::ArrayType *aty = new hy::ArrayType();
    aty->type = ty;

    llvm::ArrayType *llvm_aty = dyn_cast<llvm::ArrayType>(ty);
    aty->at = llvm_aty;
    aty->length.set_const(llvm_aty->getNumElements());

    aty->element_type = specification_handle_type(
        state, llvm_aty->getElementType(), nullptr, os, offset);

    // yuhao: todo support mode 2
    // the value of the array

    result = aty;
    break;
  }
  case llvm::Type::StructTyID: {
    // yuhao: handle the case that it is a struct
    hy::StructType *sty = new hy::StructType();
    sty->type = ty;

    llvm::StructType *llvm_sty = dyn_cast<llvm::StructType>(ty);
    sty->st = llvm_sty;

    if (llvm_sty->isPacked()) {
      sty->is_packed = true;
    }

    uint64_t temp_offset = offset;
    for (auto element : llvm_sty->elements()) {
      hy::Type *temp =
          specification_handle_type(state, element, nullptr, os, temp_offset);
      if (temp != nullptr) {
        sty->fields.push_back(temp);
      }
      temp_offset += kmodule->targetData->getTypeStoreSize(element);
      if (temp_offset >= os->size) {
        break;
      }
    }

    result = sty;
    break;
  }
  default: {
    hy_log(debug, "output_arguments: unsupported type");
  }
  }

  return result;
}

// yuhao: check whether the ucmo has possible types
// 1. if the ucmo has one type, use the type of the ucmo
// 2. if the ucmo has multiple types with different offset, c
// onstruct a new struct type
// and the fields of the struct type are the types of the ucmo
// 3. if the ucmo does not have a type, use array type
uint64_t
Executor::specification_handle_ucmo(ExecutionState &state,
                                    under_constrained_memory_object *ucmo,
                                    hy::PointerType *pty) {

  std::string str;
  int64_t debug = -1;

  // yuhao: try to get the os of the ucmo
  ObjectPair op;
  bool success = get_memory_object(op, state, ucmo);

  if (!success) {
    // yuhao: for deabug
    hy_log(2, "can not find memory object");
    return 0;
  }

  // yuhao: update direction
  if (success) {
    const ObjectState *os = op.second;
    hy::Direction direction = check_direction(os);
    pty->update_direction(direction);
  }

  //yuhao: debug
  // if (success) {
  //   hy_log(debug, "address");
  //   const MemoryObject *mo = op.first;
  //   hy_dump(debug, mo->getBaseExpr()->print, str);

  //   if (state.mo_types.find(mo) != state.mo_types.end()) {
  //     hy_log(debug, "mo types");
  //     for (llvm::Type *ty : state.mo_types[mo]->types) {
  //       hy_dump(debug, ty->print, str);
  //     }
  //     hy_log(debug, "mo latest types");
  //     hy_dump(debug, state.mo_types[mo]->current_type->print, str);
  //   }

  //   hy_log(debug, "os");
  //   const ObjectState *os = op.second;
  //   hy_dump(debug, os->print, str);
  //   hy_log(debug, "os:");
  //   for (unsigned i = 0; i < os->size; i++) {
  //     ref<Expr> value = os->read8(i);
  //     value = toUnique_ucmo(state, value);
  //     hy_dump(debug, value->print, str);
  //   }
  // }

  // yuhao: todo: it is possible that there is a field in the struct is union
  // e.g., %struct.snd_seq_event
  uint64_t mode = get_ucmo_type(ucmo);
  const ObjectState *os = op.second;
  switch (mode) {
  case 1: {
    // yuhao: the ucmo has one type
    llvm::Type *ty = ucmo->type;
    // yuhao: get the value of the memory object to expr
    pty->element_type = specification_handle_type(state, ty, nullptr, os);

    break;
  }
  case 2: {
    // yuhao: the ucmo has multiple types
    hy::StructType *sty = new hy::StructType();
    sty->is_packed = true;

    hy_log(debug, "the ucmo has multiple types");
    hy_log(debug, ucmo->dump());
    uint64_t offset = 0;
    for (auto ty : ucmo->types) {

      if (ty.first < offset) {
        continue;
      }

      if (ty.first > offset) {
        auto temp = new hy::ArrayType();
        temp->length.set_const(ty.first - offset);
        sty->fields.push_back(temp);
        offset = ty.first;
      }

      hy::Type *temp = specification_handle_type(state, ty.second.first,
                                                 nullptr, os, offset);
      if (temp != nullptr) {
        sty->fields.push_back(temp);
        offset += ty.second.second;
      }
    }

    if (offset < ucmo->size) {
      auto temp = new hy::ArrayType();
      temp->length.set_const(ucmo->size - offset);
      sty->fields.push_back(temp);
    }

    pty->element_type = sty;
    break;
  }
  case 3: {
    // yuhao: the ucmo does not have a type

    if (ucmo->is_symbolic_size) {
      // yuhao: todo handle the case that the size is symbolic
      // currently, I just do not set the size
      hy_log(3, "specification_handle_ucmo: symbolic_size");
    } else {
      if (ucmo->size == 1 || ucmo->size == 2 || ucmo->size == 4 ||
          ucmo->size == 8) {
        auto temp = new hy::IntegerType();
        temp->bit_width = ucmo->size * 8;

        ref<Expr> expr = os->read(0, temp->bit_width);
        this->get_value(state, expr, &(temp->value));

        pty->element_type = temp;
      } else {
        auto temp = new hy::ArrayType();

        temp->length.set_const(ucmo->size);

        pty->element_type = temp;

        // yuhao: todo support mode 2
        // the value of the array
      }
    }

    break;
  }
  }
  return 0;
}

// yuhao: handle the case that it is a pointer
// figure out whether the argument is a pointer or not
// if it is a pointer, we need to find the memory object
// if it is not a pointer, we just need to get the value
hy::Type *Executor::specification_handle_pointer(ExecutionState &state,
                                                 llvm::Type *ty,
                                                 ref<Expr> expr) {

  // int64_t debug = -1;

  hy::PointerType *pty = nullptr;
  under_constrained_memory_object *ucmo = nullptr;

  bool is_pointer = this->is_pointer(state, ty, expr, &ucmo);
  if (is_pointer) {
    pty = new hy::PointerType();
    pty->set_type(ty);

    specification_handle_ucmo(state, ucmo, pty);

    return pty;
  } else {
    hy::IntegerType *ity = new hy::IntegerType();
    Expr::Width width = getWidthForLLVMType(ty);
    ity->set_type(ty);
    ity->bit_width = width;

    this->get_value(state, expr, &(ity->value));

    return ity;
  }
}

// yuhao: check whether the ucmo has possible types
uint64_t Executor::get_ucmo_type(under_constrained_memory_object *ucmo) {

  uint64_t size = 0;

  if (ucmo->type != nullptr) {
    return 1;
  }

  if (ucmo->types.size() == 0) {
    return 3;
  }

  size = 0;
  if (ucmo->types.find(0) != ucmo->types.end()) {
    size += kmodule->targetData->getTypeStoreSize(ucmo->types[0].first);
    if (size == (ucmo->size)) {
      ucmo->type = ucmo->types[0].first;
      return 1;
    }
  }

  size = 0;
  for (auto ty : ucmo->types) {
    if (size <=
        ty.first + kmodule->targetData->getTypeStoreSize(ty.second.first)) {
      size = ty.first + kmodule->targetData->getTypeStoreSize(ty.second.first);
    }
  }
  if (size <= (ucmo->size)) {
    return 2;
  }

  return 3;
}

// yuhao: check whether the direction of os is out
hy::Direction Executor::check_direction(const ObjectState *os) {

  // yuhao: for the direction, we need to check whether the os is flushed/write
  for (unsigned i = 0; i < os->size; i++) {
    if (os->is_byte_unflushed(i)) {
      return hy::Direction::OUT;
    }
  }
  return hy::Direction::DEFAULT;
}

// yuhao: check whether the ucmo has possible types
void Executor::add_mo_type(ExecutionState &state, const MemoryObject *mo,
                           llvm::Type *_type) {

  uint64_t size = 0;
  if (_type != nullptr && _type->isSized()) {
    size = kmodule->targetData->getTypeStoreSize(_type);
  }
  state.add_mo_type(mo, _type, size);
}

// yuhao:
void Executor::update_fork_points(ExecutionState &state, uint64_t ret) {
  for (auto &temp_fp : state.fork_points) {
    auto inst = temp_fp.first;
    if (this->fork_points.find(inst) == this->fork_points.end()) {
      this->fork_points[inst] = new fork_point();
    }
    auto fp = this->fork_points[inst];
    fp->add(temp_fp.second.first, ret, temp_fp.second.second);
  }
}

// yuhao:
void Executor::specification_guided_fork(Executor::StatePair &branches,
                                         llvm::Instruction *inst) {
  if (branches.first && branches.second) {

    // update fork points of the branches
    if (branches.first->fork_points.find(inst) ==
        branches.first->fork_points.end()) {
      branches.first->fork_points[inst] = std::make_pair(1, 1);
    } else {
      branches.first->fork_points[inst].second++;
    }
    if (branches.second->fork_points.find(inst) ==
        branches.second->fork_points.end()) {
      branches.second->fork_points[inst] = std::make_pair(0, 1);
    } else {
      branches.second->fork_points[inst].second++;
    }

    if (fork_points.find(inst) == fork_points.end()) {
      fork_points[inst] = new fork_point();
    }
    auto fp = fork_points[inst];
    hy_log(-1, "fp: " + std::to_string(fp->total_true) + " " +
                  std::to_string(fp->total_false) + " " +
                  std::to_string(fp->total_new_specifications_true) + " " +
                  std::to_string(fp->total_new_specifications_false));

    // yuhao: calculate
    double true_ratio = 10;
    double false_ratio = 10;

    if (fp->total_true > 10) {
      true_ratio =
          (double)fp->total_new_specifications_true / (double)fp->total_true;
      double adjust_ratio = 1.0;
      if (fp->total_true > 100) {
        adjust_ratio = 0.0;
      } else if (fp->total_true > 30) {
        adjust_ratio = 0.2 * (1.0 - fp->total_true * 1.0 / 100.0);
      } else {
        adjust_ratio =
            adjust_ratio * (0.2 + 1.0 - (double)fp->total_true / 30.0);
      }
    }

    if (fp->total_false > 10) {
      false_ratio =
          (double)fp->total_new_specifications_false / (double)fp->total_false;
      double adjust_ratio = 1.0;
      if (fp->total_false > 100) {
        adjust_ratio = 0.0;
      } else if (fp->total_false > 30) {
        adjust_ratio = 0.2 * (1.0 - fp->total_false * 1.0 / 100.0);
      } else {
        adjust_ratio =
            adjust_ratio * (0.2 + 1.0 - (double)fp->total_false / 30.0);
      }
      false_ratio += adjust_ratio + 0.2;
    }

    if (true_ratio == 10 && false_ratio == 10) {
      return;
    }

    double ratio = 0.0;
    bool branch = true;
    if (true_ratio > false_ratio) {
      ratio = false_ratio;
      branch = false;
    } else {
      ratio = true_ratio;
    }

    auto temp = theRNG.getDouble();
    hy_log(-1, "true_ratio: " + std::to_string(ratio) + " " +
                  std::to_string(branch) + " " + std::to_string(temp));
    if (temp > ratio) {
      if (branch) {
        branches.first->specification = false;
        terminateStateEarly(*branches.first,
                            "specifications guided fork true: " +
                                std::to_string(ratio),
                            StateTerminationType::MaxDepth);

        hy_log(1, "terminateStateEarly state: " +
                       std::to_string(branches.first->getID()));
        hy_log(1,
               " specifications guided fork true: " + std::to_string(ratio));
        branches.first = nullptr;
      } else {
        branches.second->specification = false;
        terminateStateEarly(*branches.second,
                            "specifications guided fork false: " +
                                std::to_string(ratio),
                            StateTerminationType::MaxDepth);

        hy_log(1, "terminateStateEarly state: " +
                       std::to_string(branches.second->getID()));
        hy_log(1,
               " specifications guided fork false: " + std::to_string(ratio));
        branches.second = nullptr;
      }
      return;
    }
  }
  return;
}

// yuhao:
Cell &Executor::un_eval(KInstruction *ki, unsigned index,
                        ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  assert(vnumber != -1 &&
         "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  if (vnumber < 0) {
    unsigned index = -vnumber - 2;
    return kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    StackFrame &sf = state.stack.back();
    return sf.locals[index];
  }
}

// yuhao:
MemoryObject *Executor::create_ucmo(ExecutionState &state,
                                    const std::string &name,
                                    const llvm::Value *allocSite,
                                    uint64_t type_store_size, llvm::Type *ty) {

  hy_log(-1, "create mo: " + name);
  uint64_t size = type_store_size;

  if (ty) {
    std::string str;
    str = "create mo type: ";
    hy_add_dump(-1, ty->print, str);
    size = kmodule->targetData->getTypeStoreSize(ty);
    if (auto *st = dyn_cast<StructType>(ty)) {
      auto temp_ty = st->getElementType(st->getNumElements() - 1);
      if (auto temp_at = dyn_cast<ArrayType>(temp_ty)) {
        if (temp_at->getNumElements() == 0) {
          size += 1024;
          hy_log(-1, "create_mo: create more memory for zero length array");
        }
      }
    }
    //  if (ty->isIntegerTy(8)) {
    //    klee_message("ty->isIntegerTy(8), allocate an array of 8192 chars");
    //    size = kmodule->targetData->getTypeStoreSize(ty) * 8192;
    //  }
    //  else if (ty->isPointerTy()) {
    //    // may be array of pointer
    //    klee_message("ty->isPointerTy(), allocate an array of 128 pointers");
    //    size = kmodule->targetData->getTypeStoreSize(ty) * 128;
    //  }
  }
  if (size < type_store_size) {
    size = type_store_size;
  }

  MemoryObject *mo =
      memory->allocate(size,
                       /*isLocal=*/false, /*isGlobal=*/false, &state,
                       /*allocSite=*/allocSite, /*alignment=*/8);
  add_mo_type(state, mo, ty);
  executeMakeSymbolic(state, mo, name);
  return mo;
}

// yuhao:
llvm::Module *Executor::get_module() { return this->kmodule->module.get(); }

// yuhao:
bool Executor::get_memory_object(ObjectPair &op, ExecutionState &state,
                                 ref<Expr> address) {
  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = ConstraintManager::simplifyExpr(state.constraints, address);
  }
  address = optimizer.optimizeExpr(address, true);
  // fast path: single in-bounds resolution
  bool success;
  solver->setTimeout(coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver.get(), address, op,
                                     success)) {
    address = toConstant(state, address, "resolveOne failure");
    success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(time::Span());
  return success;
}

// yuhao:
bool Executor::get_memory_object(ObjectPair &op, ExecutionState &state,
                                 under_constrained_memory_object *ucmo) {
  int64_t debug = -1;

  if (!ucmo->is_created) {
    hy_log(debug, "smo is not created");
    return false;
  }

  ref<Expr> address = ucmo->real_address;
  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = ConstraintManager::simplifyExpr(state.constraints, address);
  }
  address = optimizer.optimizeExpr(address, true);
  bool success;
  solver->setTimeout(coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver.get(), address, op,
                                     success)) {
    return false;
  }
  solver->setTimeout(time::Span());
  return success;
}

// yuhao:
ref<Expr> Executor::read_value_from_address(ExecutionState &state,
                                            const ref<Expr> &address,
                                            Expr::Width type) {
  ObjectPair op;
  bool success = get_memory_object(op, state, address);
  if (!success) {
    klee_message("not find the mo");
    return address;
  }
  const MemoryObject *mo = op.first;
  ref<Expr> offset = mo->getOffsetExpr(address);
  const ObjectState *os = op.second;
  ref<Expr> result = os->read(offset, type);
  return result;
}

// yuhao:
bool Executor::special_function(llvm::Function *f) {
  if (this->specialFunctionHandler->handlers.find(f) ==
      this->specialFunctionHandler->handlers.end()) {
    return false;
  } else {
    return true;
  }
}

// yuhao:
void Executor::multi_layer_type_analysis() {
  Module *m = kmodule->module.get();
  auto MName = StringRef(m->getName());
  GlobalCtx.Modules.push_back(std::make_pair(m, MName));
  GlobalCtx.ModuleMaps[m] = MName;

  // Build global call graph.
  CallGraphPass CGPass(&GlobalCtx);
  CGPass.run(GlobalCtx.Modules);

  for (auto callar : GlobalCtx.Callees) {
    hy_log(-1, "indirect call: " + dump_inst(callar.first));
    for (auto callee : callar.second) {
      hy_log(-1, "callee: " + callee->getName().str());
    }
  }
}

// yuhao:
void Executor::update_entry_functions() {
  for (const auto &it : spec_config.entry_functions) {
    auto func = this->kmodule->module->getFunction(it);
    if (func == nullptr) {
      hy_log(-1, "entry_functions: " + it);
      continue;
    }
    entry_functions.push(func);
  }
  spec_config.entry_functions.clear();
}

// yuhao:
std::string Executor::get_name(klee::ref<klee::Expr> value) {
  klee::ReadExpr *revalue;
  if (value->getKind() == klee::Expr::Concat) {
    auto *c_value = llvm::cast<klee::ConcatExpr>(value);
    revalue = llvm::cast<klee::ReadExpr>(c_value->getKid(0));
  } else if (value->getKind() == klee::Expr::Read) {
    revalue = llvm::cast<klee::ReadExpr>(value);
  } else {
    std::set<std::string> names;
    resolve_symbolic_expr(value, names, 1);
    if (names.size() == 1) {
      return *names.begin();
    } else {
      std::string str = "get_name: ";
      hy_add_dump(3, value->print, str);
      return "";
    }
  }
  std::string globalName = revalue->updates.root->name;
  return globalName;
}

// yuhao:
void Executor::resolve_symbolic_expr(ref<Expr> expr,
                                     std::set<std::string> &names,
                                     uint64_t count) {
  if (count > 0) {
    if (names.size() >= count) {
      return;
    }
  }

  if (expr->getKind() == klee::Expr::Read) {
    std::string name = get_name(expr);
    names.insert(name);
    return;
  } else if (expr->getKind() == klee::Expr::Concat &&
             expr->getKid(0)->getKind() == klee::Expr::Read) {
    std::string name = get_name(expr->getKid(0));
    names.insert(name);
    return;
  } else {
    unsigned kidsNum = expr->getNumKids();
    if (kidsNum == 2 && expr->getKid(0) == expr->getKid(1)) {
      resolve_symbolic_expr(expr->getKid(0), names, count);
    } else {
      for (unsigned int i = 0; i < kidsNum; i++) {
        resolve_symbolic_expr(expr->getKid(i), names, count);
      }
    }
  }
}

// yuhao:
void Executor::resolve_symbolic_expr(ref<Expr> expr,
                                     std::set<ref<Expr>> &vars) {
  if (expr->getKind() == klee::Expr::Read) {
    vars.insert(expr);
    return;
  } else if (expr->getKind() == klee::Expr::Concat &&
             cast<klee::ConcatExpr>(expr)->getLeft()->getKind() ==
                 klee::Expr::Read) {
    vars.insert(expr);
    return;
  } else {
    unsigned kidsNum = expr->getNumKids();
    if (kidsNum == 2 && expr->getKid(0) == expr->getKid(1)) {
      resolve_symbolic_expr(expr->getKid(0), vars);
    } else {
      for (unsigned int i = 0; i < kidsNum; i++) {
        resolve_symbolic_expr(expr->getKid(i), vars);
      }
    }
  }
}

// yuhao:
bool Executor::is_related(std::set<std::string> names,
                          const std::string &name) {
  for (const auto &n : names) {
    if (n.find(name) != std::string::npos) {
      return true;
    }
  }
  return false;
}

// yuhao:
bool Executor::is_all_related(std::set<std::string> names,
                              const std::string &name) {
  for (const auto &n : names) {
    if (n.find(name) == std::string::npos) {
      return false;
    }
  }
  return true;
}

// yuhao: check whether there are related constraints
bool Executor::is_related_ucmo_constraints(ExecutionState &state,
                                           std::set<ref<Expr>> vars) {
  std::set<std::string> constraint_names;
  for (const auto &expr : *state.ucmo_constraints) {
    resolve_symbolic_expr(expr, constraint_names);
  }

  std::set<std::string> var_names;
  for (const auto &expr : vars) {
    resolve_symbolic_expr(expr, var_names);
  }

  for (const auto &name : var_names) {
    if (is_related(constraint_names, name)) {
      return true;
    }
  }
  return false;
}

// yuhao:
bool Executor::backward_trace(llvm::Value *value, llvm::Type **type,
                              bool &has_offset, llvm::Instruction **base) {
  if (auto gep = dyn_cast<llvm::GetElementPtrInst>(value)) {
    has_offset = true;
    *base = gep;
    *type = gep->getSourceElementType();
    backward_trace(gep->getOperand(0), type, has_offset, base);
    return true;
  } else if (value->getType()->isPointerTy()) {
    *type = value->getType()->getPointerElementType();
    return true;
  } else {
    std::string str;
    hy_print(-1, value->print, str);
    hy_log(-1, "backward_trace: " + str + " is not valid");
    return false;
  }
}

// yuhao:
bool Executor::forward_trace(llvm::Value *value, llvm::Type **type,
                             bool &has_offset, ref<Expr> &base) {
  return false;
}

// yuhao: similar to toUnique but with smo constraint
ref<Expr> Executor::toUnique_ucmo(const ExecutionState &state, ref<Expr> &e) {
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    e = optimizer.optimizeExpr(e, true);
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(*state.ucmo_constraints, e, value,
                         state.queryMetaData)) {
      ref<Expr> cond = EqExpr::create(e, value);
      cond = optimizer.optimizeExpr(cond, false);
      if (solver->mustBeTrue(*state.ucmo_constraints, cond, isTrue,
                             state.queryMetaData) &&
          isTrue) 
        result = value;
    }
    solver->setTimeout(time::Span());
  }

  return result;
}

// yuhao: similar to toUnique but with cond
ref<Expr> Executor::toUnique(const ExecutionState &state, ref<Expr> &new_cond,
                             ref<Expr> &e) {
  ref<Expr> result = e;

  ConstraintSet *new_constraints = new ConstraintSet(state.constraints);
  ConstraintManager c(*new_constraints);
  c.addConstraint(new_cond);

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    e = optimizer.optimizeExpr(e, true);
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(*new_constraints, e, value, state.queryMetaData)) {
      ref<Expr> cond = EqExpr::create(e, value);
      cond = optimizer.optimizeExpr(cond, false);
      if (solver->mustBeTrue(*new_constraints, cond, isTrue,
                             state.queryMetaData) &&
          isTrue)
        result = value;
    }
    solver->setTimeout(time::Span());
  }

  return result;
}

// yuhao: similar to toConstant but with smo constraint
ref<klee::ConstantExpr> Executor::get_constant_smo(ExecutionState &state,
                                                 ref<Expr> e,
                                                 const char *reason) {
  e = ConstraintManager::simplifyExpr(*state.ucmo_constraints, e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  ref<ConstantExpr> value = ConstantExpr::create(0, e->getWidth());
  
  solver->setTimeout(coreSolverTimeout);
  solver->getValue(*state.ucmo_constraints, e, value, state.queryMetaData);
  solver->setTimeout(time::Span());
  // assert(success && "FIXME: Unhandled solver failure");

  return value;
}

// yuhao: get range with smo constraints
std::pair<ref<Expr>, ref<Expr>>
Executor::to_range_smo(const ExecutionState &state, ref<Expr> &e) {
  e = optimizer.optimizeExpr(e, true);
  solver->setTimeout(coreSolverTimeout);
  auto result =
      solver->getRange(*state.ucmo_constraints, e, state.queryMetaData);
  solver->setTimeout(time::Span());
  return result;
}

// yuhao: is a meaningful range or not
bool Executor::is_meaningful_range(ref<Expr> &low, ref<Expr> &high) {
  if (isa<ConstantExpr>(low) && isa<ConstantExpr>(high) &&
      dyn_cast<ConstantExpr>(low)->getZExtValue() <
          dyn_cast<ConstantExpr>(high)->getZExtValue()) {
    if (dyn_cast<ConstantExpr>(low)->getZExtValue() == 0 &&
        dyn_cast<ConstantExpr>(high)->getZExtValue() + 1 == 0) {
      return false;
    }
    return true;
  }
  return false;
}

void Executor::get_value(ExecutionState &state, ref<Expr> expr,
                         hy::Value *value) {

  // std::set<ref<Expr>> temp;
  // temp.insert(expr);
  // bool results = is_related_ucmo_constraints(state, temp);
  // if (results == false) {
  //   value->set_no_constraints();
  //   return;
  // }

  expr = toUnique_ucmo(state, expr);
  if (auto *ce = dyn_cast<ConstantExpr>(expr)) {
    // yuhao: constant
    value->set_const(ce->getZExtValue());
    return;
  }

  // yuhao: get possible range
  std::pair<ref<Expr>, ref<Expr>> range = to_range_smo(state, expr);
  if (is_meaningful_range(range.first, range.second)) {
    ref<Expr> temp_const = get_constant_smo(state, expr, "for range value");
    if (auto *ce = dyn_cast<ConstantExpr>(temp_const)) {
      // yuhao: constant
      value->set_const(ce->getZExtValue());
    }
    value->set_range(dyn_cast<ConstantExpr>(range.first)->getZExtValue(),
                     dyn_cast<ConstantExpr>(range.second)->getZExtValue());
    return;
  }
  return;
}

bool Executor::is_pointer(ExecutionState &state, llvm::Type *ty, ref<Expr> expr,
                          under_constrained_memory_object **ucmo) {
  std::string str;
  int64_t debug = -1;

  Expr::Width width = getWidthForLLVMType(ty);
  if (width != Context::get().getPointerWidth()) {
    return false;
  }

  ref<Expr> arg_value_ucmo = toUnique_ucmo(state, expr);
  auto *ce = dyn_cast<ConstantExpr>(arg_value_ucmo);
  if (ce == nullptr) {
    return false;
  }

  hy_log(debug, "value: " + std::to_string(ce->getZExtValue()));

  *ucmo = find_ucmo_by_base_address(state, arg_value_ucmo);
  if (*ucmo == nullptr) {
    hy_log(debug, "not find smo");
    return false;
  }

  return true;
}

// yuhao: find under constrained memory object with the same base address
// if not find, create a new one
under_constrained_memory_object *
Executor::create_ucmo_by_base_address(ExecutionState &state,
                                      ref<Expr> base_address) {
  under_constrained_memory_object *smo = nullptr;

  hy_log(-1, "Executor::find_smo_base: create new smo");
  smo = new under_constrained_memory_object();
  smo->base_address = base_address;
  state.under_constrained_memory_objects[base_address] = smo;
  return smo;
}

under_constrained_memory_object *
Executor::find_ucmo_by_base_address(ExecutionState &state,
                                    ref<Expr> base_address) {
  under_constrained_memory_object *ucmo = nullptr;
  under_constrained_memory_object *possible_ucmo = nullptr;
  int64_t debug = -1;

  ucmo = state.find_ucmo_by_symbolic_base_address(base_address);

  // if find smo but smo is not created, use it later when no other smo is found
  if (ucmo != nullptr) {
    possible_ucmo = ucmo;
  }

  if (ucmo == nullptr || ucmo->is_created == false) {
    ref<Expr> temp = toUnique_ucmo(state, base_address);
    std::string str;
    str = "Executor::try to find_ucmo_base1: ";
    hy_add_dump(debug, temp->print, str);
    ucmo = state.find_ucmo_by_concrete_real_address(temp);

    if (ucmo != nullptr) {
      possible_ucmo = ucmo;
    }
  }

  if (ucmo == nullptr) {
    ucmo = possible_ucmo;
  }

  return ucmo;
}

// yuhao: find under constrained memory object including the address
// 1. smo with the same base address and created mo
// 2. smo within the range and created mo
// 3. smo with the closest base address and created mo
// using unique base address
under_constrained_memory_object *
Executor::find_ucmo_flexible(ExecutionState &state, ref<Expr> base_address,
                             ref<Expr> address) {

  int64_t debug = -1;

  under_constrained_memory_object *ucmo = nullptr;
  under_constrained_memory_object *possible_ucmo = nullptr;

  if (isa<klee::ConstantExpr>(base_address)) {
    return nullptr;
  }

  ref<Expr> temp = toUnique_ucmo(state, base_address);
  ref<Expr> temp2 = toUnique_ucmo(state, address);
  std::string str;
  str = "Executor::try to find_smo_base2: ";
  hy_add_dump(debug, temp2->print, str);

  // try to find smo based on address and range
  // if base address or final located in the range of smo, return the smo
  ucmo = state.find_ucmo_by_address_and_range(temp, temp2);

  if (ucmo != nullptr) {
    possible_ucmo = ucmo;
  }

  // yuhao: if the base addres is symbolic and can be unique to concrete
  // try to find the smo close to the base address but outside the range
  // only when the base address is symbolic
  // for resize and relocate
  if ((ucmo == nullptr || ucmo->is_created == false) &&
      !isa<ConstantExpr>(base_address)) {
    ref<Expr> unique_base_address = toUnique_ucmo(state, base_address);
    if (isa<ConstantExpr>(unique_base_address)) {
      std::string str;
      str = "Executor::try to find_smo_base3: ";
      hy_add_dump(debug, unique_base_address->print, str);

      uint64_t unique_base_address_int =
          dyn_cast<ConstantExpr>(unique_base_address)->getZExtValue();

      under_constrained_memory_object *max = nullptr;
      under_constrained_memory_object *min = nullptr;

      for (auto &&it : state.under_constrained_memory_objects) {
        if (it.second->is_created == false ||
            !isa<ConstantExpr>(it.second->real_address)) {
          continue;
        }
        uint64_t smo_addr =
            dyn_cast<ConstantExpr>(it.second->real_address)->getZExtValue();
        if (unique_base_address_int < smo_addr) {
          if (max == nullptr) {
            max = it.second;
          } else {
            uint64_t max_addr =
                dyn_cast<ConstantExpr>(max->real_address)->getZExtValue();
            if (smo_addr < max_addr) {
              max = it.second;
            }
          }
        } else if (unique_base_address_int > smo_addr) {
          if (min == nullptr) {
            min = it.second;
          } else {
            uint64_t min_addr =
                dyn_cast<ConstantExpr>(min->real_address)->getZExtValue();
            if (smo_addr > min_addr) {
              min = it.second;
            }
          }
        }
      }

      std::vector<under_constrained_memory_object *> possible_smos;
      if (min != nullptr && max != nullptr) {
        uint64_t max_addr =
            dyn_cast<ConstantExpr>(max->real_address)->getZExtValue();
        uint64_t min_addr =
            dyn_cast<ConstantExpr>(min->real_address)->getZExtValue();
        if (unique_base_address_int - min_addr <
            max_addr - unique_base_address_int) {
          possible_smos.push_back(min);
          possible_smos.push_back(max);
        } else {
          possible_smos.push_back(max);
          possible_smos.push_back(min);
        }
      } else if (min != nullptr) {
        possible_smos.push_back(min);
      } else if (max != nullptr) {
        possible_smos.push_back(max);
      } else {
      }

      for (under_constrained_memory_object *temp : possible_smos) {
        ref<Expr> _constraint =
            EqExpr::create(temp->base_address, temp->real_address);
        ref<Expr> temp_unique_base_address =
            toUnique(state, _constraint, base_address);
        if (isa<ConstantExpr>(temp_unique_base_address)) {
          uint64_t temp_unique_base_address_int =
              dyn_cast<ConstantExpr>(temp_unique_base_address)->getZExtValue();
          if (temp_unique_base_address_int == unique_base_address_int) {
            ucmo = temp;
            break;
          }
        }
      }
    }
  }

  if (ucmo == nullptr) {
    ucmo = possible_ucmo;
  }

  return ucmo;
}

// yuhao:
ref<Expr> Executor::find_base_address(ExecutionState &state, ref<Expr> address,
                                      KInstruction *target, int64_t operand,
                                      llvm::Type **type) {

  int64_t debug = -1;
  std::string str;
  ref<Expr> base_address = address;

  if (!isa<klee::ConstantExpr>(base_address) && target != nullptr) {

    hy_log(debug,
           "state: " + std::to_string(state.getID()) + ": symbolic address");
    hy_dump(debug, target->inst->print, str);

    str = "smo base address 1: ";
    hy_add(debug, base_address->print, str);
    hy_log(debug, str);

    // yuhao: find the llvm base address based on llvm instruction
    llvm::Value *llvm_addr = nullptr;
    llvm_addr = target->inst->getOperand(operand);
    bool has_offset = false;
    llvm::Instruction *base_inst;
    bool success2 = false;
    success2 = backward_trace(llvm_addr, type, has_offset, &base_inst);
    if (success2) {
      str = "backward trace mo_type: ";
      hy_add(debug, (*type)->print, str);
      hy_log(debug, str);
    }
    if (has_offset) {
      if (state.base_address.find(base_inst) != state.base_address.end()) {
        base_address = state.base_address[base_inst];
      } else {
        hy_log(3, "not find base_inst in baseAddress");
        return base_address;
      }
    }

    str = "smo base address after backward_trace: ";
    hy_add(debug, base_address->print, str);
    hy_log(debug, str);
  }

  // yuhao: based on symbolic address
  // yuhao: find the base address recursively if the address is symbolic
  std::set<ref<Expr>> temp_addresses;
  temp_addresses.insert(base_address);
  while (state.symbolic_address_map.find(base_address) !=
         state.symbolic_address_map.end()) {
    auto temp = state.symbolic_address_map[base_address];
    if (temp_addresses.find(temp) != temp_addresses.end()) {
      break;
    }
    temp_addresses.insert(temp);
    base_address = temp;
  }

  str = "smo base address after recursively: ";
  hy_add(debug, base_address->print, str);
  hy_log(debug, str);

  return base_address;
}

void Executor::record_linked_list(ExecutionState &state, KInstruction *ki) {
  std::string str;
  int64_t debug = -1;
  llvm::Type *type = ki->inst->getOperand(0)->getType();

  if (!type->isPointerTy()) {
    return;
  }
  type = type->getPointerElementType();

  if (!type->isPointerTy()) {
    return;
  }
  type = type->getPointerElementType();

  if (!type->isStructTy()) {
    return;
  }
  llvm::StructType *st = llvm::cast<llvm::StructType>(type);

  if (!(st->getName().str() == "struct.list_head")) {
    return;
  }

  hy_log(debug, "record_linked_list1");

  llvm::Value *llvm_addr = ki->inst->getOperand(0);

  if (!isa<llvm::GetElementPtrInst>(llvm_addr)) {
    return;
  }
  llvm::GetElementPtrInst *gep = llvm::cast<llvm::GetElementPtrInst>(llvm_addr);
  type = gep->getSourceElementType();

  hy_log(debug, "record_linked_list2");
  hy_dump(debug, type->print, str);

  if (!type->isStructTy()) {
    return;
  }
  st = llvm::cast<llvm::StructType>(type);

  if (!(st->getName().str() == "struct.list_head")) {
    return;
  }

  hy_log(debug, "record_linked_list3");
  ref<Expr> entry = eval(ki, 0, state).value;
  llvm::Value *offset = gep->getOperand(2);
  if (llvm::isa<llvm::ConstantInt>(offset)) {
    int64_t ap = llvm::cast<llvm::ConstantInt>(offset)->getSExtValue();
    if (ap == 1) {
      entry = SubExpr::create(entry, ConstantExpr::create(8, Expr::Int64));
    }
  }

  ref<Expr> next = getDestCell(state, ki).value;
  if (next.isNull()) {
    return;
  }
  str = "record_linked_list: entry: ";
  hy_add_dump(debug, entry->print, str);
  state.linked_list_map_next[next] = entry;
  str = "record_linked_list: next: ";
  hy_add_dump(debug, next->print, str);
  ref<Expr> prev = AddExpr::create(next, ConstantExpr::create(8, Expr::Int64));
  state.linked_list_map_prev[prev] = entry;
  str = "record_linked_list: prev: ";
  hy_add_dump(debug, prev->print, str);
  return;
}

void Executor::maintain_linked_list(ExecutionState &state, KInstruction *ki,
                                    bool is_write, MemoryObject *mo,
                                    ref<Expr> address) {
  std::string str;
  int64_t debug = -1;
  llvm::Type *type = ki->inst->getOperand(is_write ? 1 : 0)->getType();
  if (!type->isPointerTy()) {
    return;
  }
  type = type->getPointerElementType();
  if (!type->isPointerTy()) {
    return;
  }
  type = type->getPointerElementType();
  if (!type->isStructTy()) {
    return;
  }
  llvm::StructType *st = llvm::cast<llvm::StructType>(type);
  if (st->getName().str() == "struct.list_head") {
    hy_log(debug, "maintain_linked_list");
    const ObjectState *os = state.addressSpace.findObject(mo);
    ObjectState *wos = state.addressSpace.getWriteable(mo, os);
    if (state.linked_list_map_next.find(address) !=
        state.linked_list_map_next.end()) {
      ref<Expr> prev = state.linked_list_map_next[address];
      wos->write(ConstantExpr::create(8, Expr::Int64), prev);
      str = "maintain_linked_list: prev: ";
      hy_add_dump(debug, prev->print, str);
    }
    if (state.linked_list_map_prev.find(address) !=
        state.linked_list_map_prev.end()) {
      ref<Expr> next = state.linked_list_map_prev[address];
      wos->write(ConstantExpr::create(0, Expr::Int64), next);
      str = "maintain_linked_list: next: ";
      hy_add_dump(debug, next->print, str);
    }
  }
}

// yuhao: analysis for the copy_from_user, copy_to_user, memdup_user
void Executor::type_analysis(ExecutionState &state, KInstruction *ki,
                             Function *f, std::vector<ref<Expr>> &arguments) {

  int64_t debug = -1;
  std::string str;

  // yuhao: perform analysis for type info of user input
  // handle the basic situation: mo type <-> user input with offset
  auto name = f->getName();
  if (name == "_copy_from_user") {
    hy_log(debug, "type_analysis: _copy_from_user: state: " +
                      std::to_string(state.id));
    ref<Expr> to_address = arguments[0];
    ref<Expr> from_address = arguments[1];
    hy_dump(debug, to_address->print, str);
    hy_dump(debug, from_address->print, str);

    ObjectPair op;
    bool success = get_memory_object(op, state, to_address);
    if (!success) {
      hy_log(2, "type_analysis: not find to_address");
      return;
    }

    const MemoryObject *to_mo = op.first;
    hy_dump(debug, to_mo->getBaseExpr()->print, str);
    // yuhao: only handle the situation that to_address is the base address of
    // to_mo

    ref<Expr> check = EqExpr::create(to_mo->getBaseExpr(), to_address);
    check = toUnique_ucmo(state, check);

    if (check->isFalse()) {
      hy_log(2, "type_analysis: to_address != to_mo->getBaseExpr()");
      return;
    }

    llvm::Type *type = nullptr;
    ref<Expr> base_address =
        find_base_address(state, from_address, ki, 2, &type);
    under_constrained_memory_object *ucmo =
        find_ucmo_flexible(state, base_address, from_address);
    if (ucmo == nullptr) {
      ucmo = create_ucmo_by_base_address(state, base_address);
      hy_log(debug, "type_analysis: smo is null");
      hy_dump(debug, from_address->print, str);
    }
    ref<Expr> offset = SubExpr::create(from_address, base_address);
    offset = toUnique_ucmo(state, offset);

    // yuhao: only handle the situation that offset is a constant
    if (!isa<ConstantExpr>(offset)) {
      hy_log(2, "type_analysis: !isa<ConstantExpr>(offset)");
      return;
    }
    uint64_t offset_int = dyn_cast<ConstantExpr>(offset)->getZExtValue();

    state.mo_relationship_map[to_mo] = std::make_pair(ucmo, offset_int);
    hy_log(debug, "mo_relationship_map address");
    hy_dump(debug, to_mo->getBaseExpr()->print, str);
    hy_dump(debug, ucmo->base_address->print, str);

    if (state.mo_types.find(to_mo) != state.mo_types.end()) {
      auto mt = state.mo_types[to_mo];
      llvm::Type *ty = state.mo_types[to_mo]->current_type;
      if (ty != nullptr) {
        hy_log(debug, "type_analysis: _copy_from_user: add init type: size: " +
                          std::to_string(mt->types.size()));
        hy_dump(debug, ty->print, str);
        uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
        ucmo->add_ucmo_type(offset_int, ty, size);
      }
    }

  } else if (name == "_copy_to_user") {
    hy_log(debug, "type_analysis: _copy_to_user");

    hy_log(1, "output_arguments before _copy_to_user");
    specification_handle(state);

    ref<Expr> to_address = arguments[0];
    ref<Expr> from_address = arguments[1];

    ObjectPair op;
    bool success = get_memory_object(op, state, from_address);
    if (!success) {
      return;
    }

    // yuhao: only handle the situation that from_address is the base address of
    // yuhao: todo: handle the situation that from_address is not the base
    const MemoryObject *from_mo = op.first;
    if (from_address != from_mo->getBaseExpr()) {
      return;
    }

    llvm::Type *type = nullptr;
    ref<Expr> base_address = find_base_address(state, to_address, ki, 1, &type);
    under_constrained_memory_object *ucmo =
        find_ucmo_flexible(state, base_address, to_address);
    if (ucmo == nullptr) {
      ucmo = create_ucmo_by_base_address(state, base_address);
      hy_log(debug, "type_analysis: smo is null");
      hy_dump(debug, to_address->print, str);
    }
    ref<Expr> offset = SubExpr::create(to_address, base_address);
    if (!isa<ConstantExpr>(offset)) {
      return;
    }
    int64_t offset_int = dyn_cast<ConstantExpr>(offset)->getZExtValue();
    state.mo_relationship_map[from_mo] = std::make_pair(ucmo, offset_int);

    if (state.mo_types.find(from_mo) != state.mo_types.end()) {
      auto mt = state.mo_types[from_mo];
      llvm::Type *ty = mt->current_type;
      if (ty != nullptr) {
        hy_log(debug, "type_analysis: _copy_to_user: add init type: size: " +
                          std::to_string(mt->types.size()));
        hy_dump(debug, ty->print, str);
        uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
        ucmo->add_ucmo_type(offset_int, ty, size);
      }
    }
  } else {

  }
}