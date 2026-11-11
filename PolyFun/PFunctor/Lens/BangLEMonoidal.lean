/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.BangLE
public import PolyFun.PFunctor.Lens.Duoidal

/-!
# The monoidal structure of the graded exponential

The graded exponential `bangLE n` of `Lens/BangLE.lean` is lax monoidal for the parallel product:
a multiset of pairs of directions demands the multiset of its first components and the multiset
of its second components (`Lens.bangLETensor`), and the unit `y` maps into `bangLE n y`
(`Lens.bangLEUnit`). This file proves the laws that make `bangLE` a graded linear exponential
comonad in the sense of Katsumata (*A double category theoretic analysis of graded linear
exponential comonads*, FoSSaCS 2018), in the form of Definition 6 of Barbarossa and Pistone
(*Tropical mathematics and the lambda-calculus I*, arXiv:2311.15704), together with the graded
comonad and commutative comonoid laws of `Lens/BangLE.lean`. Its axioms (7) and (9) are stated
here with the unit `Lens.bangLEUnit` and the indices that make them type-check.

## Main results

* `Lens.bangLETensor_natural`, `Lens.bangLETensor_assoc`, `Lens.bangLETensor_unit_left`,
  `Lens.bangLETensor_unit_right`, `Lens.bangLETensor_comm` — each `bangLE n` is a symmetric lax
  monoidal functor;
* `Lens.bangLESub_tensor`, `Lens.bangLESub_unit` — the inclusions of grades are monoidal;
* `Lens.bangLECounit_tensor`, `Lens.bangLEComult_tensor`, `Lens.bangLEWeak_tensor`,
  `Lens.bangLEContr_tensor` and their `_unit` forms — counit, comultiplication, weakening and
  contraction are monoidal;
* `Lens.bangLEWeak_natural`, `Lens.bangLEContr_sub`, `Lens.bangLEComult_sub` — naturality of
  weakening, and of contraction and comultiplication in the grades;
* `Lens.bangLEWeak_comult`, `Lens.bangLEMap_weak_comult`, `Lens.bangLEContr_comult`,
  `Lens.bangLEMap_contr_comult` — the comultiplication against weakening and contraction, with the
  grade equations `0 * s = 0`, `s * 0 = 0` and distributivity as inclusions of grades.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

open CategoryTheory

namespace PFunctor

namespace Lens

section Monoidal

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- The lax monoidal structure of `bangLE n` for `⊗`: a multiset of pairs of directions demands the
multisets of its first and of its second components. -/
def bangLETensor (n : ℕ∞) (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Lens (bangLE n P ⊗ bangLE n Q) (bangLE n (P ⊗ Q)) :=
  id ⇆ fun (x : P.A × Q.A) (s : {m : Multiset (P.B x.1 × Q.B x.2) // (m.card : ℕ∞) ≤ n}) =>
    (⟨s.1.map Prod.fst, by simpa using s.2⟩, ⟨s.1.map Prod.snd, by simpa using s.2⟩)

/-- The unit of the lax monoidal structure of `bangLE n`. -/
def bangLEUnit (n : ℕ∞) : Lens y.{uA, uB} (bangLE n y.{uA, uB}) :=
  id ⇆ fun _ _ => PUnit.unit

end Monoidal

/-- Unfold the lenses of this file and normalise maps and binds of multisets. -/
local macro "bangLE_tac" : tactic => `(tactic| (
  dsimp only [Lens.comp, Lens.id, bangLEMap, bangLETensor, bangLEUnit, bangLESub, bangLECounit,
    bangLEComult, bangLEWeak, bangLEContr, tensorMap, Lens.Equiv.tensorAssoc,
    Lens.Equiv.tensorComm, Lens.Equiv.tensorY, Lens.Equiv.yTensor,
    Lens.Equiv.tensorTensorTensorComm, Function.comp, Prod.map, id_eq]
  repeat
    first
      | erw [Multiset.map_map]
      | erw [Multiset.map_bind]
      | erw [Multiset.bind_map]
      | erw [Multiset.map_add]
      | erw [Multiset.add_bind]
      | erw [Multiset.bind_add]
  all_goals first
    | rfl
    | exact Multiset.map_id _
    | exact Multiset.bind_zero _
    | exact (Multiset.map_map Prod.fst Prod.snd _).symm
    | exact (Multiset.map_map Prod.snd Prod.snd _).symm))

section Monoidal

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- The monoidal structure is natural. -/
theorem bangLETensor_natural {P' : PFunctor.{uA₃, uB₃}} {Q' : PFunctor.{uA₄, uB₄}} (n : ℕ∞)
    (f : Lens P P') (g : Lens Q Q') :
    bangLEMap n (f ⊗ₗ g) ∘ₗ bangLETensor n P Q =
      bangLETensor n P' Q' ∘ₗ (bangLEMap n f ⊗ₗ bangLEMap n g) := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- Associativity of the monoidal structure. -/
theorem bangLETensor_assoc (n : ℕ∞) :
    bangLEMap n Lens.Equiv.tensorAssoc.toLens ∘ₗ bangLETensor n (P ⊗ Q) R ∘ₗ
        (bangLETensor n P Q ⊗ₗ Lens.id (bangLE n R)) =
      bangLETensor n P (Q ⊗ R) ∘ₗ (Lens.id (bangLE n P) ⊗ₗ bangLETensor n Q R) ∘ₗ
        Lens.Equiv.tensorAssoc.toLens := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨⟨_, _⟩, _⟩ => funext fun _ => ?_
  refine Prod.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)) (Subtype.ext ?_) <;> bangLE_tac

/-- Left unit law of the monoidal structure. -/
theorem bangLETensor_unit_left (n : ℕ∞) :
    bangLEMap n Lens.Equiv.yTensor.toLens ∘ₗ bangLETensor n y.{uA, uB} Q ∘ₗ
        (bangLEUnit n ⊗ₗ Lens.id (bangLE n Q)) =
      Lens.Equiv.yTensor.toLens := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext rfl (Subtype.ext ?_)
  bangLE_tac

/-- Right unit law of the monoidal structure. -/
theorem bangLETensor_unit_right (n : ℕ∞) :
    bangLEMap n Lens.Equiv.tensorY.toLens ∘ₗ bangLETensor n P y.{uA, uB} ∘ₗ
        (Lens.id (bangLE n P) ⊗ₗ bangLEUnit n) =
      Lens.Equiv.tensorY.toLens := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) rfl
  bangLE_tac

/-- The monoidal structure is symmetric. -/
theorem bangLETensor_comm (n : ℕ∞) :
    bangLEMap n (Lens.Equiv.tensorComm P Q).toLens ∘ₗ bangLETensor n P Q =
      bangLETensor n Q P ∘ₗ (Lens.Equiv.tensorComm (bangLE n P) (bangLE n Q)).toLens := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- The inclusions of grades are monoidal. -/
theorem bangLESub_tensor {m n : ℕ∞} (h : n ≤ m) :
    bangLESub h (P ⊗ Q) ∘ₗ bangLETensor m P Q =
      bangLETensor n P Q ∘ₗ (bangLESub h P ⊗ₗ bangLESub h Q) := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- The inclusions of grades preserve the unit. -/
theorem bangLESub_unit {m n : ℕ∞} (h : n ≤ m) :
    bangLESub h y.{uA, uB} ∘ₗ bangLEUnit m = bangLEUnit n :=
  rfl

/-- The counit is monoidal. -/
theorem bangLECounit_tensor :
    bangLECounit (P ⊗ Q) ∘ₗ bangLETensor 1 P Q = bangLECounit P ⊗ₗ bangLECounit Q := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- The counit preserves the unit. -/
theorem bangLECounit_unit : bangLECounit y.{uA, uB} ∘ₗ bangLEUnit 1 = Lens.id y.{uA, uB} :=
  rfl

/-- The comultiplication is monoidal. -/
theorem bangLEComult_tensor (m n : ℕ∞) :
    bangLEComult m n (P ⊗ Q) ∘ₗ bangLETensor (m * n) P Q =
      bangLEMap m (bangLETensor n P Q) ∘ₗ bangLETensor m (bangLE n P) (bangLE n Q) ∘ₗ
        (bangLEComult m n P ⊗ₗ bangLEComult m n Q) := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- The comultiplication preserves the unit. -/
theorem bangLEComult_unit (m n : ℕ∞) :
    bangLEComult m n y.{uA, uB} ∘ₗ bangLEUnit (m * n) =
      bangLEMap m (bangLEUnit n) ∘ₗ bangLEUnit m :=
  rfl

end Monoidal

section Comonoid

variable {P Q : PFunctor.{uA, uB}}

/-- Weakening is natural. -/
theorem bangLEWeak_natural (l : Lens P Q) : bangLEWeak Q ∘ₗ bangLEMap 0 l = bangLEWeak P :=
  rfl

/-- Weakening is monoidal. -/
theorem bangLEWeak_tensor :
    bangLEWeak (P ⊗ Q) ∘ₗ bangLETensor 0 P Q =
      (Lens.Equiv.yTensor.toLens : Lens (y.{uA, uB} ⊗ y.{uA, uB}) y.{uA, uB}) ∘ₗ
        (bangLEWeak P ⊗ₗ bangLEWeak Q) :=
  rfl

/-- Weakening preserves the unit. -/
theorem bangLEWeak_unit : bangLEWeak y.{uA, uB} ∘ₗ bangLEUnit 0 = Lens.id y.{uA, uB} :=
  rfl

/-- Contraction is monoidal. -/
theorem bangLEContr_tensor (m n : ℕ∞) :
    bangLEContr m n (P ⊗ Q) ∘ₗ bangLETensor (m + n) P Q =
      (bangLETensor m P Q ⊗ₗ bangLETensor n P Q) ∘ₗ
        (Lens.Equiv.tensorTensorTensorComm (bangLE m P) (bangLE n P) (bangLE m Q)
          (bangLE n Q)).toLens ∘ₗ (bangLEContr m n P ⊗ₗ bangLEContr m n Q) := by
  refine Lens.ext _ _ (fun _ => rfl) fun ⟨_, _⟩ => funext fun _ => ?_
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> bangLE_tac

/-- Contraction preserves the unit. -/
theorem bangLEContr_unit (m n : ℕ∞) :
    bangLEContr m n y.{uA, uB} ∘ₗ bangLEUnit (m + n) =
      (bangLEUnit m ⊗ₗ bangLEUnit n) ∘ₗ Lens.Equiv.yTensor.invLens :=
  rfl

/-- Contraction is natural in the grades. -/
theorem bangLEContr_sub {m m' n n' : ℕ∞} (h₁ : m' ≤ m) (h₂ : n' ≤ n) :
    (bangLESub h₁ P ⊗ₗ bangLESub h₂ P) ∘ₗ bangLEContr m n P =
      bangLEContr m' n' P ∘ₗ bangLESub (add_le_add h₁ h₂) P :=
  rfl

/-- The comultiplication is natural in the grades. -/
theorem bangLEComult_sub {m m' n n' : ℕ∞} (h₁ : m' ≤ m) (h₂ : n' ≤ n) :
    bangLEMap m' (bangLESub h₂ P) ∘ₗ bangLESub h₁ (bangLE n P) ∘ₗ bangLEComult m n P =
      bangLEComult m' n' P ∘ₗ bangLESub (mul_le_mul' h₁ h₂) P := by
  refine Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext ?_
  bangLE_tac

/-! ## The comultiplication against weakening and contraction -/

/-- Weakening after the comultiplication at grade `0` is weakening. -/
theorem bangLEWeak_comult (s : ℕ∞) :
    bangLEWeak (bangLE s P) ∘ₗ bangLEComult 0 s P =
      bangLEWeak P ∘ₗ bangLESub (zero_mul s).ge P := by
  refine Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => ?_
  rfl

/-- The exponential of weakening after the comultiplication is the unit after weakening. -/
theorem bangLEMap_weak_comult (s : ℕ∞) :
    bangLEMap s (bangLEWeak P) ∘ₗ bangLEComult s 0 P =
      bangLEUnit s ∘ₗ bangLEWeak P ∘ₗ bangLESub (mul_zero s).ge P := by
  refine Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext ?_
  bangLE_tac

/-- Contraction commutes with the comultiplication, up to `(r + r') * s ≤ r * s + r' * s`. -/
theorem bangLEContr_comult (r r' s : ℕ∞) :
    (bangLEComult r s P ⊗ₗ bangLEComult r' s P) ∘ₗ bangLEContr (r * s) (r' * s) P =
      bangLEContr r r' (bangLE s P) ∘ₗ bangLEComult (r + r') s P ∘ₗ
        bangLESub (add_mul r r' s).le P := by
  refine Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext ?_
  bangLE_tac

/-- The exponential of contraction after the comultiplication, up to
`s * (r + r') ≤ s * r + s * r'`. -/
theorem bangLEMap_contr_comult (r r' s : ℕ∞) :
    bangLETensor s (bangLE r P) (bangLE r' P) ∘ₗ (bangLEComult s r P ⊗ₗ bangLEComult s r' P) ∘ₗ
        bangLEContr (s * r) (s * r') P =
      bangLEMap s (bangLEContr r r' P) ∘ₗ bangLEComult s (r + r') P ∘ₗ
        bangLESub (mul_add s r r').le P := by
  refine Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Subtype.ext ?_
  bangLE_tac

end Comonoid

end Lens

end PFunctor
