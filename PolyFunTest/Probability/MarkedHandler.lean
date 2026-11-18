/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.MarkedHandler

/-!
# A private-state setup charge

The handler makes a request on its first invocation. A second invocation sees the updated
private state. The same interpretation retains the implementation kernel's separate counter.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace PolyFunTest.Probability.MarkedHandler

abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

private noncomputable def marks : MarkedKernelHandler Tick Nat Nat := fun _ =>
  Kernel.deterministic (fun n => ((), n + 1, 1)) Measurable.of_discrete

private instance (a : Tick.A) : IsSubprobabilityKernel (marks a) := by
  unfold marks
  infer_instance

private def setup : Handler.Stateful (FreeM Tick) Bool Tick := fun _ => StateT.mk fun ready =>
  if ready then pure ((), true) else FreeM.liftBind () fun _ => pure ((), true)

private def twice : FreeM Tick Unit := .liftBind () fun _ => .liftBind () fun _ => pure ()

private noncomputable abbrev implemented : MarkedKernelHandler Tick (Bool × Nat) Nat :=
  marks.comapStateful setup (fun _ => Measurable.of_discrete)

example (n : Nat) : implemented.joint twice (false, n) =
    Measure.dirac ((), (true, n + 1), 1) := by
  rw [← marks.joint_run setup (fun _ => Measurable.of_discrete) twice false n]
  change (marks.joint (FreeM.liftBind () fun _ => FreeM.pure ((), true)) n).map
    MarkedKernelHandler.threadMark = _
  rw [FreeM.liftBind_eq, marks.joint_bind, marks.joint_lift, marks, Kernel.deterministic_apply]
  rw [Measure.dirac_bind Measurable.of_discrete]
  change ((marks.joint (pure ((), true)) (n + 1)).map
    (MarkedKernelHandler.prepend 1)).map MarkedKernelHandler.threadMark = _
  rw [marks.joint_pure, Measure.map_dirac' (MarkedKernelHandler.measurable_prepend (1 : Nat)),
    Measure.map_dirac' MarkedKernelHandler.measurable_threadMark]
  rfl

end PolyFunTest.Probability.MarkedHandler
