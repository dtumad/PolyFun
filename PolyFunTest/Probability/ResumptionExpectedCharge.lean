/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Measure

/-!
# Expected charge with silent divergence and private state

A client calls a service twice and then diverges. The service uses a visible target operation
only on the first call. Its private state and the price of silent steps both affect the reading.
-/

public section

open MeasureTheory PFunctor PFunctor.Resumption
open scoped ENNReal

namespace PolyFunTest.Probability.ResumptionExpectedCharge

abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- A request with no returning mass still costs seven, even with infinite terminal credit. -/
theorem charge_before_zero_kernel (next : Unit → Resumption Tick Unit) :
    Resumption.expectedCharge (P := Tick) (fun _ => 0) (fun _ (_ : Unit) => 7)
      (Resumption.query () next) (fun _ _ => ⊤) () = 7 := by
  rw [Resumption.expectedCharge_query (P := Tick) (S := Unit) _ _ (fun _ => measurable_const) _ _ _
    (fun _ => measurable_const)]
  simp

private noncomputable def answer (_ : Tick.A) : Measure Unit := Measure.dirac ()

private def setup : Handler.Stateful (FreeM Tick) Bool Tick := fun _ => StateT.mk fun ready =>
  if ready then pure ((), true)
  else FreeM.liftBind () fun _ => pure ((), true)

private def client : ITree Tick Unit :=
  ITree.query () fun _ => ITree.query () fun _ => ITree.diverge

private noncomputable abbrev charge : Tick.A → Bool → ℝ≥0∞ :=
  setup.expectedCharge answer (fun _ => 1)
private noncomputable abbrev law : KernelHandler Tick Bool :=
  setup.toKernelHandler answer (fun _ => Measurable.of_discrete)

private theorem law_apply (ready : Bool) :
    law () ready = Measure.dirac ((), true) := by
  cases ready with
  | true => exact FreeM.measureFold_pure (P := Tick) answer _
  | false =>
    change FreeM.measureFold answer (FreeM.liftBind () fun _ => pure ((), true)) = _
    rw [FreeM.measureFold_liftBind (P := Tick) answer _ _ Measurable.of_discrete.aemeasurable]
    simp [answer]

private theorem charge_apply (ready : Bool) :
    charge () ready = if ready then 0 else 1 := by
  cases ready <;>
    simp [charge, Handler.Stateful.expectedCharge, setup, answer, StateT.run_mk]

/-- The actual stateful interpreter pays exactly once before diverging. -/
example (ret : Unit → MeasurableExpectation Bool) :
    ITree.denote (fun z : Unit × Bool => (ret z.1).1 z.2) (ITree.expectedChargeAlgebra answer
        (fun _ => 1))
      ((ITree.interp (m := StateT Bool (ITree Tick))
        (fun a s => ((setup a).run s).toITree) client).run false) = 1 := by
  rw [ITree.expectedCharge_interp_run (Q := Tick) answer (fun _ => 1) setup
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete)]
  change ITree.expectedCharge law charge _ client ret false = 1
  unfold client
  rw [ITree.expectedCharge_query (P := Tick) law charge (fun _ => Measurable.of_discrete)
    () _ ret false 0, law_apply]
  simp only [lintegral_dirac]
  rw [ITree.expectedCharge_query (P := Tick) law charge (fun _ => Measurable.of_discrete)
    () _ ret true 0, law_apply]
  simp [charge_apply]

/-- A single paid silent guard and a divergent chain of paid guards have different costs. -/
example (ret : Unit → MeasurableExpectation Bool) (s : Bool) :
    ITree.expectedCharge law charge (fun _ => Measurable.of_discrete)
      (ITree.step (ITree.pure ())) ret s 1 = 1 + (ret ()).1 s ∧
    ITree.expectedCharge law charge (fun _ => Measurable.of_discrete)
      ITree.diverge ret s 1 = ⊤ := by
  constructor
  · simp
  · exact ITree.expectedCharge_diverge_of_pos _ _ _ _ _ zero_lt_one

private def spendThenDiverge : PFunctor.Handler (StateT Unit (ITree Tick)) Tick :=
  fun _ _ => ITree.query () fun _ => ITree.diverge

private noncomputable abbrev target : KernelHandler Tick Bool :=
  KernelHandler.ofFun (fun _ s => ((), !s)) (fun _ => Measurable.of_discrete)

/-- A divergent operation spends four in its target and returns no private state. -/
private theorem divergent_implementation :
    ITree.handlerCharge spendThenDiverge target (fun _ _ => 4) (fun _ => measurable_const)
      () ((), false) = 4 ∧
    ITree.handlerReturnLaw spendThenDiverge target () ((), false) = 0 := by
  constructor
  · unfold ITree.handlerCharge spendThenDiverge
    rw [ITree.expectedCharge_query (P := Tick) (T := Bool)]
    simp
  · simp [ITree.handlerReturnLaw, spendThenDiverge, ITree.returnedKernel_query (P := Tick)]

/-- The operational interpreter still counts a divergent implementation's paid work. The
client's infinite return credit never becomes payable. -/
example : ITree.expectedCharge target (fun _ _ => 4) (fun _ => measurable_const)
    ((ITree.interp spendThenDiverge (ITree.query () fun _ => ITree.pure ())).run ())
    (fun _ => ⟨fun _ => ⊤, measurable_const⟩) false = 4 := by
  let ret : Unit → MeasurableExpectation (Unit × Bool) := fun _ => ⟨fun _ => ⊤, measurable_const⟩
  have sim := ITree.expectedCharge_interp_run_unbounded spendThenDiverge target
    (fun _ _ => 4) (fun _ => measurable_const)
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete)
    (ITree.query () fun _ => ITree.pure ()) ret () false
  rw [ITree.expectedCharge_query (P := Tick) (T := Unit × Bool)] at sim
  simpa [ret, ITree.handlerKernel, divergent_implementation.1, divergent_implementation.2] using sim

private def toggleBoth : PFunctor.Handler (StateT Bool (ITree Tick)) Tick :=
  fun _ s => ITree.query () fun _ => ITree.pure ((), !s)

private def oneCall : ITree Tick Unit := ITree.query () fun _ => ITree.pure ()

/-- A request with infinite cost can still return. The executed client's terminal law
records the implementation state and the target state in their respective positions. -/
example :
    ITree.handlerCharge toggleBoth target (fun _ _ => ⊤) (fun _ => measurable_const)
      () (false, true) = ⊤ ∧
    ((ITree.returnedKernel target ((ITree.interp toggleBoth oneCall).run false)) true).map
      MeasurableEquiv.prodAssoc = Measure.dirac ((), true, false) := by
  constructor
  · unfold ITree.handlerCharge toggleBoth
    rw [ITree.expectedCharge_query (P := Tick) (T := Bool)]
    exact top_add _
  · rw [ITree.returnedKernel_interp_run toggleBoth target (fun _ => Measurable.of_discrete)]
    simp only [oneCall, ITree.returnedKernel_query (P := Tick), ITree.returnedKernel_pure,
      ITree.handlerKernel, ProbabilityTheory.Kernel.coe_mk, ITree.handlerReturnLaw, toggleBoth,
      target, KernelHandler.ofFun, ProbabilityTheory.Kernel.deterministic_apply]
    simp [Measure.dirac_bind Measurable.of_discrete]
    rfl

private def hiddenCall {S : Type} (spend : S → Bool) :
    PFunctor.Handler (StateT S (ITree Tick)) Tick :=
  fun _ s => if spend s then ITree.query () fun _ => ITree.diverge else ITree.diverge

/-- The handler may branch on an arbitrary private predicate. Every branch diverges, so the
return law is measurable, and four bounds its charge without measurability of the predicate. -/
example {S : Type} [MeasurableSpace S] (spend : S → Bool) (tree : ITree Tick Unit)
    (s : S) (t : Bool) :
    ITree.expectedCharge target (fun _ _ => 4) (fun _ => measurable_const)
      ((ITree.interp (hiddenCall spend) tree).run s) (fun _ => ⊥) t ≤
    ITree.expectedCharge (P := Tick) (fun _ => 0) (fun _ _ => 4) (fun _ => measurable_const)
      tree (fun _ => ⊥) (s, t) := by
  have hlaw (a : Tick.A) : ITree.handlerReturnLaw (hiddenCall spend) target a = 0 := by
    funext st
    cases hs : spend st.1 <;>
      simp [ITree.handlerReturnLaw, hiddenCall, hs, ITree.returnedKernel_query (P := Tick)]
  have hm (a : Tick.A) : Measurable (ITree.handlerReturnLaw (hiddenCall spend) target a) := by
    rw [hlaw]
    exact measurable_const
  have hcost (a : Tick.A) (st : S × Bool) :
      ITree.handlerCharge (hiddenCall spend) target (fun _ _ => 4) (fun _ => measurable_const)
        a st ≤ 4 := by
    cases hs : spend st.1 <;>
      simp [ITree.handlerCharge, hiddenCall, hs, ITree.expectedCharge_query (P := Tick)]
  have sim := ITree.expectedCharge_interp_run_unbounded_le (hiddenCall spend) target
    (fun _ _ => 4) (fun _ => measurable_const) hm (fun _ _ => 4) (fun _ => measurable_const)
    hcost tree (fun _ => ⊥) s t
  have hker : ITree.handlerKernel (hiddenCall spend) target hm = fun _ => 0 := by
    funext a
    ext1 st
    exact congrFun (hlaw a) st
  rw [hker] at sim
  exact sim

end PolyFunTest.Probability.ResumptionExpectedCharge
