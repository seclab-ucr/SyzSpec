//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "ExecutionState.h"

#include "Memory.h"

#include "klee/Expr/Expr.h"
#include "klee/Module/Cell.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Support/Casting.h"
#include "klee/Support/OptionCategories.h"

// yuhao:
#include "klee/Utils/llvm_related.h"
#include "klee/Utils/log.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#include <stdarg.h>
#include <utility>

using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool> DebugLogStateMerge(
    "debug-log-state-merge", cl::init(false),
    cl::desc("Debug information for underlying state merging (default=false)"),
    cl::cat(MergeCat));
}

/***/

std::uint32_t ExecutionState::nextID = 1;

/***/

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0), 
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs), 
    // yuhao: add loop_map
    loop_map(s.loop_map) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

/***/

// yuhao:
ExecutionState::ExecutionState() {
  this->ucmo_constraints = new ConstraintSet;
  setID();
}

// yuhao: 
void ExecutionState::set_function(KFunction *kf) {
  pc = kf->instructions;
  prevPC = pc;
  while (!stack.empty())
    popFrame();
  pushFrame(nullptr, kf);
  // hy_log(-1, "stack size: " + std::to_string(stack.size()));
}

ExecutionState::ExecutionState(KFunction *kf, MemoryManager *mm)
    : pc(kf->instructions), prevPC(pc) {
  pushFrame(nullptr, kf);
  setID();
  if (mm->stackFactory && mm->heapFactory) {
    stackAllocator = mm->stackFactory.makeAllocator();
    heapAllocator = mm->heapFactory.makeAllocator();
  }
}

ExecutionState::~ExecutionState() {
  for (const auto &cur_mergehandler: openMergeStack){
    cur_mergehandler->removeOpenState(this);
  }

  while (!stack.empty()) popFrame();

  // yuhao: delete under constrained memory objects
  for (auto it : under_constrained_memory_objects) {
    delete it.second;
  }

  // yuhao: delete mo types
  for (auto it : mo_types) {
    delete it.second;
  }
}

ExecutionState::ExecutionState(const ExecutionState& state):
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),
    depth(state.depth),
    addressSpace(state.addressSpace),
    stackAllocator(state.stackAllocator),
    heapAllocator(state.heapAllocator),
    constraints(state.constraints),
    pathOS(state.pathOS),
    symPathOS(state.symPathOS),
    coveredLines(state.coveredLines),
    symbolics(state.symbolics),
    cexPreferences(state.cexPreferences),
    arrayNames(state.arrayNames),
    openMergeStack(state.openMergeStack),
    steppedInstructions(state.steppedInstructions),
    instsSinceCovNew(state.instsSinceCovNew),
    unwindingInformation(state.unwindingInformation
                             ? state.unwindingInformation->clone()
                             : nullptr),
    //yuhao
    id(state.id),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    //yuhao
    base_address(state.base_address),
    symbolic_address_map(state.symbolic_address_map),
    linked_list_map_prev(state.linked_list_map_prev),
    linked_list_map_next(state.linked_list_map_next) {
  for (const auto &cur_mergehandler: openMergeStack)
    cur_mergehandler->addOpenState(this);

  // yuhao: copy under constrained memory objects
  for (auto it : state.under_constrained_memory_objects) {
    under_constrained_memory_object *ucmo =
        new under_constrained_memory_object();

    ucmo->base_address = it.second->base_address;
    ucmo->size = it.second->size;

    ucmo->type = it.second->type;

    ucmo->is_created = it.second->is_created;
    if (ucmo->is_created) {
      ucmo->real_address = it.second->real_address;
    }

    for (auto type : it.second->types) {
      ucmo->types[type.first] = type.second;
    }

    ucmo->is_symbolic_size = it.second->is_symbolic_size;
    if (ucmo->is_symbolic_size) {
      ucmo->symbolic_size = it.second->symbolic_size;
    }

    under_constrained_memory_objects.insert(std::make_pair(it.first, ucmo));
  }
  this->ucmo_constraints = nullptr;
  update_ucmo_constraints();

  // yuhao: copy mo types
  for (auto it : state.mo_types) {
    MemoryObjectType *mt = new MemoryObjectType;
    for (auto type : it.second->types) {
      mt->types.insert(type);
    }
    mt->current_type = it.second->current_type;
    mo_types.insert(std::make_pair(it.first, mt));
  }

  for (auto it : state.mo_relationship_map) {
    const MemoryObject *mo = it.first;
    ref<Expr> base_address = it.second.first->base_address;
    int64_t offset = it.second.second;
    if (under_constrained_memory_objects.find(base_address) !=
        under_constrained_memory_objects.end()) {
      under_constrained_memory_object *ucmo =
          under_constrained_memory_objects[base_address];
      mo_relationship_map[mo] = std::make_pair(ucmo, offset);
    } else {
      hy_log(
          3,
          "state: " + std::to_string(this->getID()) +
              " copy constructor: mo_relationship_map: base_address not found");
    }
  }

  // yuhao: specification guided fork
  for (auto it : state.fork_points) {
    this->fork_points[it.first] =
        std::make_pair(it.second.first, it.second.second);
  }
}

ExecutionState *ExecutionState::branch() {
  depth++;

  auto *falseState = new ExecutionState(*this);
  falseState->setID();
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  // yuhao: debug
  std::string str;
  uint64_t debug = 1;
  hy_log(debug, "branch at: " + dump_inst(this->prevPC->inst));
  hy_dump(-1, this->prevPC->inst->print, str);
  hy_log(debug, "trueState is: " + std::to_string(this->getID()));
  hy_log(debug, "falseState is: " + std::to_string(falseState->getID()));

  return falseState;
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.emplace_back(StackFrame(caller, kf));
}

void ExecutionState::popFrame() {
  const StackFrame &sf = stack.back();
  for (const auto *memoryObject : sf.allocas) {
    deallocate(memoryObject);
    addressSpace.unbindObject(memoryObject);
  }
  stack.pop_back();
}

void ExecutionState::deallocate(const MemoryObject *mo) {
  if (!stackAllocator || !heapAllocator)
    return;

  auto address = reinterpret_cast<void *>(mo->address);
  if (mo->isLocal) {
    stackAllocator.free(address, std::max(mo->size, mo->alignment));
  } else {
    heapAllocator.free(address, std::max(mo->size, mo->alignment));
  }
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) {
  symbolics.emplace_back(ref<const MemoryObject>(mo), array);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second.get();
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second.get();
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?

  if (symbolics != b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }

  std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  std::set< ref<Expr> > bConstraints(b.constraints.begin(), 
                                     b.constraints.end());
  std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  std::set_intersection(aConstraints.begin(), aConstraints.end(),
                        bConstraints.begin(), bConstraints.end(),
                        std::inserter(commonConstraints, commonConstraints.begin()));
  std::set_difference(aConstraints.begin(), aConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(aSuffix, aSuffix.end()));
  std::set_difference(bConstraints.begin(), bConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(bSuffix, bSuffix.end()));
  if (DebugLogStateMerge) {
    llvm::errs() << "\tconstraint prefix: [";
    for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
                                        ie = commonConstraints.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tA suffix: [";
    for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
                                        ie = aSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tB suffix: [";
    for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
                                        ie = bSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
  }

  // We cannot merge if addresses would resolve differently in the
  // states. This means:
  // 
  // 1. Any objects created since the branch in either object must
  // have been free'd.
  //
  // 2. We cannot have free'd any pre-existing object in one state
  // and not the other

  if (DebugLogStateMerge) {
    llvm::errs() << "\tchecking object states\n";
    llvm::errs() << "A: " << addressSpace.objects << "\n";
    llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  }
    
  std::set<const MemoryObject*> mutated;
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  for (; ai!=ae && bi!=be; ++ai, ++bi) {
    if (ai->first != bi->first) {
      if (DebugLogStateMerge) {
        if (ai->first < bi->first) {
          llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
        } else {
          llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
        }
      }
      return false;
    }
    if (ai->second.get() != bi->second.get()) {
      if (DebugLogStateMerge)
        llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
      mutated.insert(ai->first);
    }
  }
  if (ai!=ae || bi!=be) {
    if (DebugLogStateMerge)
      llvm::errs() << "\t\tmappings differ\n";
    return false;
  }
  
  // merge stack

  ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  for (std::set< ref<Expr> >::iterator it = aSuffix.begin(), 
         ie = aSuffix.end(); it != ie; ++it)
    inA = AndExpr::create(inA, *it);
  for (std::set< ref<Expr> >::iterator it = bSuffix.begin(), 
         ie = bSuffix.end(); it != ie; ++it)
    inB = AndExpr::create(inB, *it);

  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if (!av || !bv) {
        // if one is null then by implication (we are at same pc)
        // we cannot reuse this local, so just ignore
      } else {
        av = SelectExpr::create(inA, av, bv);
      }
    }
  }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(), 
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly && 
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      wos->write(i, SelectExpr::create(inA, av, bv));
    }
  }

  constraints = ConstraintSet();

  ConstraintManager m(constraints);
  for (const auto &constraint : commonConstraints)
    m.addConstraint(constraint);
  m.addConstraint(OrExpr::create(inA, inB));

  return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << "(";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      if (ai->hasName())
        out << ai->getName().str() << "=";

      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (isa_and_nonnull<ConstantExpr>(value)) {
        out << value;
      } else {
        out << "symbolic";
      }
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}

void ExecutionState::addConstraint(ref<Expr> e) {
  ConstraintManager c(constraints);
  c.addConstraint(e);

  // yuhao:
  add_ucmo_constraints(e);
}

void ExecutionState::addCexPreference(const ref<Expr> &cond) {
  cexPreferences = cexPreferences.insert(cond);
}

// yuhao: find under constrained memory object based on symbolic address
under_constrained_memory_object *
ExecutionState::find_ucmo_by_symbolic_base_address(ref<Expr> base_address) {
  if (under_constrained_memory_objects.find(base_address) !=
      under_constrained_memory_objects.end()) {
    return under_constrained_memory_objects[base_address];
  }
  return nullptr;
}

// yuhao: find created under constrained memory object based on real address
under_constrained_memory_object *
ExecutionState::find_ucmo_by_concrete_real_address(ref<Expr> real_address) {
  under_constrained_memory_object *ucmo = nullptr;

  uint64_t real_addr = 0;

  if (isa<ConstantExpr>(real_address)) {
    real_addr = dyn_cast<ConstantExpr>(real_address)->getZExtValue();
  } else {
    return nullptr;
  }

  for (auto temp : under_constrained_memory_objects) {
    if (temp.second->is_created == false ||
        !isa<ConstantExpr>(temp.second->real_address)) {
      continue;
    }
    uint64_t ucmo_addr =
        dyn_cast<ConstantExpr>(temp.second->real_address)->getZExtValue();
    if (ucmo_addr == real_addr) {
      ucmo = temp.second;
      return ucmo;
    }
  }
  return nullptr;
}

// yuhao: find under constrained memory object based on constant address
under_constrained_memory_object *
ExecutionState::find_ucmo_by_address_and_range(ref<Expr> base_address,
                                              ref<Expr> final_address) {
  under_constrained_memory_object *ucmo = nullptr;

  bool check_base = false;
  bool check_final = false;
  uint64_t base_addr = 0;
  uint64_t final_addr = 0;

  if (isa<ConstantExpr>(base_address)) {
    check_base = true;
    base_addr = dyn_cast<ConstantExpr>(base_address)->getZExtValue();
  }
  if (isa<ConstantExpr>(final_address)) {
    check_final = true;
    final_addr = dyn_cast<ConstantExpr>(final_address)->getZExtValue();
  }

  for (auto temp : under_constrained_memory_objects) {
    if (temp.second->is_created == false ||
        !isa<ConstantExpr>(temp.second->real_address)) {
      continue;
    }
    uint64_t ucmo_addr =
        dyn_cast<ConstantExpr>(temp.second->real_address)->getZExtValue();
    if (check_base) {
      if (ucmo_addr <= base_addr &&
          base_addr <= (ucmo_addr + temp.second->size)) {
        ucmo = temp.second;
        return ucmo;
      }
    }
    if (check_final) {
      if (ucmo_addr <= final_addr &&
          final_addr <= (ucmo_addr + temp.second->size)) {
        ucmo = temp.second;
        return ucmo;
      }
    }
  }
  return ucmo;
}

// yuhao:
std::string under_constrained_memory_object::dump() const {
  std::string ret = "\n";
  uint64_t  debug = -1;

  ret += "base_address: ";
  hy_add(debug, base_address->print, ret);
  ret += "\n";

  ret += "size: " + std::to_string(size) + "\n";

  if (type != nullptr) {
    ret += "type: ";
    hy_add(debug, type->print, ret);
    ret += "\n";
  }

  ret += "is_created: " + std::to_string(is_created) + "\n";

  for (auto type : types) {
    ret += "offset: " + std::to_string(type.first) + " type: ";
    hy_add(debug, type.second.first->print, ret);
    ret += " size: " + std::to_string(type.second.second);
    ret += "\n";
  }

  ret += "is_symbolic_size: " + std::to_string(is_symbolic_size) + "\n";
  if (is_symbolic_size) {
    ret += "symbolic_size: ";
    hy_add(debug, symbolic_size->print, ret);
    ret += "\n";
  }

  return ret;
}

// yuhao: update the size of under constrained memory object
// if the size is larger than the current size
void under_constrained_memory_object::update_ucmo_size(llvm::Type *_type,
                                                       uint64_t _size) {
  if (_size >= this->size) {
    this->size = _size;
    this->type = _type;
  }
}

// yuhao:
void under_constrained_memory_object::update_ucmo_real_address(
    ref<Expr> _real_address) {
  this->is_created = true;
  this->real_address = _real_address;
}

void under_constrained_memory_object::update_ucmo_symbolic_size(
    ref<Expr> _symbolic_size) {
  this->is_symbolic_size = true;
  this->symbolic_size = _symbolic_size;
}

// yuhao: because it would add useless type during the symbolic execution
// we need to record the most useful one, e.g., structure
void under_constrained_memory_object::add_ucmo_type(uint64_t offset,
                                                    llvm::Type *_type,
                                                    uint64_t _size) {
  if (types.find(offset) != types.end()) {
    auto temp = types[offset];

    if (temp.first->isArrayTy()) {

      if (_type->isArrayTy()) {
        if (_size >= types[offset].second) {
          types[offset] = std::make_pair(_type, _size);
        }
      } else if (_type->isStructTy()) {
        types[offset] = std::make_pair(_type, _size);
      }

    } else if (temp.first->isStructTy()) {

      if (temp.first->getStructName().startswith("struct.")) {

        if (_type->isStructTy() &&
            _type->getStructName().startswith("struct.")) {

          if (_size >= types[offset].second) {
            types[offset] = std::make_pair(_type, _size);
          }

        }

      } else if (temp.first->getStructName().startswith("union.")) {

        if (_type->isStructTy() &&
            _type->getStructName().startswith("struct.")) {
          types[offset] = std::make_pair(_type, _size);
        } else if (_type->isStructTy() &&
                   _type->getStructName().startswith("union.")) {

          if (_size >= types[offset].second) {
            types[offset] = std::make_pair(_type, _size);
          }

        }
      }
    }
  } else {
    types[offset] = std::make_pair(_type, _size);
  }
}

// yuhao:
void ExecutionState::add_ucmo_constraints(ref<Expr> e) {
  ConstraintManager c(*ucmo_constraints);
  c.addConstraint(e);
}

// yuhao:
bool ExecutionState::add_ucmo_constraints(under_constrained_memory_object *ucmo) {
  std::string str;

  ConstraintManager c(*ucmo_constraints);
  ref<Expr> base_address = ucmo->base_address;
  ref<Expr> real_address = ucmo->real_address;
  ref<Expr> _constraint = EqExpr::create(base_address, real_address);
  str = "state: " + std::to_string(this->getID()) + " add_ucmo_constraints2: ";
  hy_add_dump(-1, _constraint->print, str);

  ref<Expr> simplified = c.simplifyExpr(*ucmo_constraints, _constraint);
  if (isa<ConstantExpr>(simplified) &&
      !dyn_cast<ConstantExpr>(simplified)->isTrue()) {
    return false;
  }
  c.addConstraint(_constraint);
  return true;
}

// yuhao:
bool ExecutionState::update_ucmo_constraints() {
  if (this->ucmo_constraints != nullptr) {
    delete this->ucmo_constraints;
  }
  this->ucmo_constraints = new ConstraintSet(this->constraints);

  bool result = true;
  for (auto ucmo : under_constrained_memory_objects) {
    if (ucmo.second->is_created == false) {
      continue;
    }
    result = add_ucmo_constraints(ucmo.second);
    if (result == false) {
      break;
    }
  }

  std::string str;
  hy_log(-1, "state: " + std::to_string(this->getID()) +
                 " update_ucmo_constraints:");
  for (auto c : this->constraints) {
    hy_dump(-1, c->print, str);
  }
  return result;
}

// yuhao: add type to memory object
// we only consider derived types, not consider primitive type
// now they are struct, array, function pointer or pointer of them
void ExecutionState::add_mo_type(const MemoryObject *mo, llvm::Type *_type, uint64_t _size) {

  int64_t debug = -1;
  std::string str;

  if (_type == nullptr) {
    return;
  }

  str = "state: " + std::to_string(this->getID()) + " add_type: ";
  hy_add_dump(debug, _type->print, str);

  // yuhao: if the type is a pointer, we need to find the real type
  // should not do this and store pointer type
  // yuhao: todo may has issue
  auto temp = _type;
  while (temp->isPointerTy()) {
    temp = temp->getPointerElementType();
  }

  if (_type->isStructTy() || _type->isArrayTy() || _type->isFunctionTy() ||
      temp->isStructTy() || temp->isArrayTy() || temp->isFunctionTy()) {

    str = "state: " + std::to_string(this->getID()) + " add_type: add: ";
    hy_add_dump(debug, _type->print, str);

    MemoryObjectType *mt = nullptr;
    if (mo_types.find(mo) == mo_types.end()) {
      mt = new MemoryObjectType;
      mo_types.insert(std::make_pair(mo, mt));
    } else {
      mt = mo_types[mo];
    }

    mt->types.insert(_type);
    mt->current_type = _type;

    // yuhao: update the type of under constrained memory object
    // always use the latest type, do not keep the old type
    if (mo_relationship_map.find(mo) != mo_relationship_map.end()) {
      under_constrained_memory_object *ucmo = mo_relationship_map[mo].first;
      uint64_t offset = mo_relationship_map[mo].second;
      ucmo->add_ucmo_type(offset, _type, _size);
      hy_log(debug, "state: " + std::to_string(this->getID()) + " add_type: read add: ");
      hy_dump(debug, ucmo->base_address->print, str);
      hy_dump(debug, _type->print, str);
    }
  }
}

// yuhao:
bool ExecutionState::is_possible_mo(const MemoryObject *mo, llvm::Type *_type) {
    
    // yuhao: if there is not allocSite for the memory,
    // we assume it is not a possible target
    if (!mo->allocSite) {
      return false;
    }

    // yuhao: if the allocSite is a alloc inst,
    // we assume it is not a possible target
    // todo: yuhao: check it later
    // if (llvm::isa<llvm::AllocaInst>(allocSite)) {
    //   return false;
    // }

    // yuhao: if there is no type constraint for the memory,
    // we assume it is a possible target
    if (!_type) {
      return true;
    }

    // yuhao: if the allocSite is a call site, and there is no possible type
    // we assume it is a possible target
    // e.g., malloc

    std::set<llvm::Type *> *types = nullptr;
    if (mo_types.find(mo) != mo_types.end()) {
      types = &mo_types[mo]->types;
    }

    if (llvm::isa<llvm::CallBase>(mo->allocSite) && (types == nullptr || types->empty())) {
      return true;
    }

    if (types == nullptr) {
      return false;
    }

    // yuhao: if the type is in the type set, it is a possible target
    if (types->find(_type) != types->end()) {
      return true;
    } else {
      return false;
    }
}