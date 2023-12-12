include "tomasulo.dfy"
// prod_machine.dfy


module prod_machine {

  import opened common

  import opened specification

  import opened tomasulo
  datatype ProductState = ProductState(spec: specification.State, impl: tomasulo.State) {
    ghost predicate inv()
    {
      spec.inv() &&
      impl.inv() &&
      spec.pc == impl.pc &&
      spec.inst_mem == impl.inst_mem &&
      spec.init_regs_ == impl.init_regs_ &&
      spec.last_writer_ == impl.last_writer_ &&
      spec.taints_[..spec.pc] == impl.taints_[..impl.pc]
    }

    static ghost function init(reg_init: seq<word>, inst_init: seq<Instruction>): (p: ProductState)
      requires |reg_init| == reg_count
      requires |inst_init| == pc_max
      ensures p.inv()
    {
      ProductState(spec := specification.State.init(reg_init, inst_init), impl := tomasulo.State.init(reg_init, inst_init))
    }

    ghost function next(): (p': ProductState)
      requires inv()
      requires !(spec.done() && impl.done())
      ensures p'.inv()
    {
      var impl' := impl.next();
      var spec' := if impl'.pc == impl.pc then spec else spec.next();
      ProductState(spec', impl')
    }

    lemma outcome_equivalence()
      requires inv() && spec.done() && impl.done()
      ensures forall i: reg_index :: impl.reg_file[i] == Word(spec.reg_file[i])
    {
      equal_taints_implies_equal_outputs(pc_max);
    }

    lemma equal_taints_implies_equal_outputs(pc: pc_range)
      requires inv() && spec.done() && impl.done()
      ensures forall i | 0 <= i < pc :: impl.outputs_[i] == Word(spec.outputs_[i])
    {
      if pc > -1 {
        assert impl.valid_location(pc - 1);
        equal_taints_implies_equal_outputs(pc - 1);
      }
    }
  }
}
