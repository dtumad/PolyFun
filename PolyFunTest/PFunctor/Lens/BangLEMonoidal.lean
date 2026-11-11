/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.BangLEMonoidal

/-!
# Examples for the monoidal structure of the graded exponential

Regression tests: the monoidal map of `bangLE` splits a concrete multiset of pairs into its
components, and the lax monoidal and comonoid laws specialize to a concrete polynomial.
-/

@[expose] public section

namespace PFunctor.BangLEMonoidalTest

open PFunctor

/-- The concrete polynomial `y^Bool`. -/
abbrev P₀ : PFunctor.{0, 0} := purePower Bool

/-- A multiset of two pairs of directions, of size at most `2`. -/
def pairs : (bangLE 2 (P₀ ⊗ P₀)).B (PUnit.unit, PUnit.unit) :=
  ⟨{(true, false), (false, false)}, by decide⟩

/-- The monoidal map splits the pairs into their first and second components. -/
example : ((Lens.bangLETensor 2 P₀ P₀).toFunB (PUnit.unit, PUnit.unit) pairs).1.1 =
    {true, false} :=
  rfl

/-- The second components keep their multiplicity. -/
example : ((Lens.bangLETensor 2 P₀ P₀).toFunB (PUnit.unit, PUnit.unit) pairs).2.1 =
    {false, false} :=
  rfl

/-- Contraction is monoidal at concrete grades. -/
example : Lens.bangLEContr 1 2 (P₀ ⊗ P₀) ∘ₗ Lens.bangLETensor (1 + 2) P₀ P₀ =
    (Lens.bangLETensor 1 P₀ P₀ ⊗ₗ Lens.bangLETensor 2 P₀ P₀) ∘ₗ
      (Lens.Equiv.tensorTensorTensorComm (bangLE 1 P₀) (bangLE 2 P₀) (bangLE 1 P₀)
        (bangLE 2 P₀)).toLens ∘ₗ (Lens.bangLEContr 1 2 P₀ ⊗ₗ Lens.bangLEContr 1 2 P₀) :=
  Lens.bangLEContr_tensor 1 2

/-- The comultiplication against contraction at concrete grades. -/
example : Lens.bangLETensor 2 (bangLE 1 P₀) (bangLE 3 P₀) ∘ₗ
      (Lens.bangLEComult 2 1 P₀ ⊗ₗ Lens.bangLEComult 2 3 P₀) ∘ₗ
        Lens.bangLEContr (2 * 1) (2 * 3) P₀ =
    Lens.bangLEMap 2 (Lens.bangLEContr 1 3 P₀) ∘ₗ Lens.bangLEComult 2 (1 + 3) P₀ ∘ₗ
      Lens.bangLESub (mul_add 2 1 3).le P₀ :=
  Lens.bangLEMap_contr_comult 1 3 2

end PFunctor.BangLEMonoidalTest
