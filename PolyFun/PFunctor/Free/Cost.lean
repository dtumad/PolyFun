/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.PFunctor.Bound
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Interaction cost of free programs

A *charge* `c : P.A → ω` prices each call of an interface `P` in an ordered additive monoid `ω`.
It is paid when the call is made, before its answer arrives. This module gives the two readings
of a charge on a free program `x : FreeM P α` and the bridges between them.

* `IsChargeBound x c B s`: with `s` already spent, the amount spent along every branch of `x`,
  call by call, stays at most `B`. It is the fold of `OpSpec.budget c B`, whose carrier is a
  predicate on the amount spent so far, so a call at `a` asks `s + c a ≤ B` and no subtraction or
  existential is involved. The spent amount defaults to `0`. It makes sense in any ordered
  additive monoid, including `ℕ`, vectors `ι → ℕ` and records of counters.
* `cost c x`: the worst-case cost of `x`, the fold of `OpSpec.charge c` with zero leaves, in a
  complete lattice such as `ℕ∞`, `ℝ≥0∞` or `ι → ℕ∞`. `costWith c x k` charges each leaf `a` the
  extra amount `k a`, which makes sequencing exact: `cost c (x >>= f)` is
  `costWith c x fun a => cost c (f a)`.

The value form is the computational one: its equations reduce the cost of a concrete `do` program
to arithmetic by `simp`. The bridges `isChargeBound_of_cost_le` and `cost_le_of_isChargeBound`
translate between the two readings in canonically ordered monoids; the second needs addition to
distribute over nonempty suprema (`AddSupDistrib`, which holds in `ℕ∞`, `ℝ≥0∞` and pointwise).
`isChargeBound_iff_cost_natCast_le` is the natural-number budget as a bound on the cost in `ℕ∞`.

Both readings transport along lenses (`IsChargeBound.mapLens`, `cost_mapLens_le`) and through
free handlers, where each call is charged the worst case of its implementation
(`IsChargeBound.liftM`, `cost_liftM_le`, `handlerCost`). Budgets combine componentwise in product
and family cost types (`isChargeBound_prod_iff`, `isChargeBound_pi_iff`), push forward along
monotone additive maps (`IsChargeBound.map`), and relate to the guard-and-update budgets of
`IsRollBound` (`isChargeBound_iff_isRollBound`, `isChargeBound_iff_isRollBound_tsub`).

A query whose answer type is empty is still charged: both readings count the call itself, not
only the calls on completed paths.
-/

@[expose] public section

universe uA uB uA₂ uB₂ v v' w w'

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- The worst-case charge reading: a call at `a` costs `c a`, followed by the worst
continuation. -/
noncomputable def charge {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R) : OpSpec P R :=
  fun a k => c a + ⨆ b, k b

@[simp]
theorem charge_apply {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R) (a : P.A)
    (k : P.B a → R) :
    charge c a k = c a + ⨆ b, k b :=
  rfl

/-- The charge reading is monotone whenever addition is. -/
theorem charge_mono {R : Type w} [CompleteLattice R] [Add R] [AddLeftMono R] (c : P.A → R) :
    (charge c).Monotone := by
  intro a k k' hk
  change c a + ⨆ b, k b ≤ c a + ⨆ b, k' b
  gcongr with b
  exact hk b

/-- The budget reading of a charge, in spent-amount form. The carrier is a predicate on the
amount spent so far: a call at `a` is admitted when the amount spent after it, `s + c a`, is at
most `B`, and each continuation starts from that amount. -/
def budget {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) : OpSpec P (ω → Prop) :=
  fun a k s => s + c a ≤ B ∧ ∀ b, k b (s + c a)

@[simp]
theorem budget_apply {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) (a : P.A)
    (k : P.B a → ω → Prop) (s : ω) :
    budget c B a k s ↔ s + c a ≤ B ∧ ∀ b, k b (s + c a) :=
  Iff.rfl

end OpSpec

/-! ## Distributivity of addition over suprema -/

/-- Addition on the left distributes over suprema of nonempty sets. This is the hypothesis under
which a structural charge bound bounds the worst-case cost (`FreeM.cost_le_of_isChargeBound`): the
bound checks every branch separately, while the cost takes the supremum first. It holds in `ℕ∞`,
in `ℝ≥0∞` and pointwise in families. -/
class AddSupDistrib (ω : Type w) [Add ω] [CompleteLattice ω] : Prop where
  add_sSup_le (a : ω) {s : Set ω} (hs : s.Nonempty) : a + sSup s ≤ ⨆ b ∈ s, a + b

theorem add_iSup_le_iSup_add {ω : Type w} [Add ω] [CompleteLattice ω] [AddSupDistrib ω]
    {ι : Sort*} [Nonempty ι] (a : ω) (f : ι → ω) : a + ⨆ i, f i ≤ ⨆ i, a + f i := by
  rw [← sSup_range]
  refine (AddSupDistrib.add_sSup_le a (Set.range_nonempty f)).trans ?_
  exact iSup₂_le fun _ ⟨i, hi⟩ => hi ▸ le_iSup (fun i => a + f i) i

instance : AddSupDistrib ℕ∞ where
  add_sSup_le _ _ hs := (ENat.add_sSup hs).le

instance {ι : Type*} {ω : ι → Type w} [∀ i, Add (ω i)] [∀ i, CompleteLattice (ω i)]
    [∀ i, AddSupDistrib (ω i)] : AddSupDistrib (∀ i, ω i) where
  add_sSup_le a s hs i := by
    have : Nonempty s := hs.to_subtype
    rw [Pi.add_apply, sSup_apply, iSup_apply]
    refine (add_iSup_le_iSup_add (a i) fun f : s => (f : ∀ i, ω i) i).trans ?_
    refine iSup_le fun f => ?_
    refine le_trans ?_ (le_iSup _ (f : ∀ i, ω i))
    rw [iSup_apply]
    exact le_iSup (fun _ : (f : ∀ i, ω i) ∈ s => (a + f) i) f.2

/-! ## Finite suprema

Worst-case costs take suprema over answer types. For finite answer types these unfold to binary
suprema, which `simp` and `norm_num` then evaluate. `iSup_bool_eq`, `iSup_option` and `iSup_sum`
are in Mathlib; the `Fin` case is below. -/

theorem _root_.Fin.iSup_succ {L : Type w} [CompleteLattice L] {n : ℕ} (f : Fin (n + 1) → L) :
    ⨆ i, f i = f 0 ⊔ ⨆ i : Fin n, f i.succ := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup f 0) (iSup_le fun j => le_iSup f _))
  induction i using Fin.cases with
  | zero => exact le_sup_left
  | succ j => exact le_sup_of_le_right (le_iSup (fun j : Fin n => f j.succ) j)

theorem _root_.Fin.iSup_zero {L : Type w} [CompleteLattice L] (f : Fin 0 → L) : ⨆ i, f i = ⊥ :=
  iSup_of_empty f

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type v} {ω : Type w}

/-! ## Structural charge bounds -/

section Bound

variable [Add ω] [LE ω] [Zero ω]

/-- `x.IsChargeBound c B s`: with `s` already spent, every call of `x` keeps the amount spent at
most `B`, where a call at `a` costs `c a`, and every leaf is reached within `B`. The spent amount
defaults to `0`. -/
def IsChargeBound (x : FreeM P α) (c : P.A → ω) (B : ω) (spent : ω := 0) : Prop :=
  wpFold (OpSpec.budget c B) x (fun _ s => s ≤ B) spent

variable {c : P.A → ω} {B s : ω}

@[simp, freeM_unfold]
theorem isChargeBound_pure_iff (a : α) :
    IsChargeBound (pure a : FreeM P α) c B s ↔ s ≤ B :=
  Iff.rfl

/-- `isChargeBound_pure_iff` for the constructor `FreeM.pure`, which `TypeTree.done` and the
recursor produce. -/
@[freeM_unfold]
theorem isChargeBound_freeM_pure_iff (a : α) :
    IsChargeBound (FreeM.pure a : FreeM P α) c B s ↔ s ≤ B :=
  Iff.rfl

@[freeM_unfold]
theorem isChargeBound_liftBind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound (FreeM.liftBind a r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBound_lift_bind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound ((FreeM.lift a).bind (α := no_index (P.B a)) r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

/-- `isChargeBound_lift_bind_iff` when results and directions share a universe. -/
theorem isChargeBound_lift_bind_iff' {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound (Bind.bind (α := no_index (P.B a)) (FreeM.lift a) r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBound_lift_iff (a : P.A) :
    IsChargeBound (α := no_index (P.B a)) (FreeM.lift a) c B s ↔ s + c a ≤ B :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

/-- A lifted object (the form in which `MonadLift P (FreeM P)` issues a call) is one call. -/
theorem isChargeBound_liftObj_iff (x : P.Obj α) :
    IsChargeBound (FreeM.liftObj x) c B s ↔ s + c x.1 ≤ B :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

/-- Sequencing, exactly: the continuation starts from whatever amount each branch of `x` has
spent. -/
theorem isChargeBound_bind_iff {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    IsChargeBound (FreeM.bind x f) c B s ↔
      wpFold (OpSpec.budget c B) x (fun a s' => IsChargeBound (f a) c B s') s := by
  unfold IsChargeBound
  rw [wpFold_bind']

@[simp]
theorem isChargeBound_bind_iff' (x : FreeM P α) (f : α → FreeM P β) :
    IsChargeBound (x >>= f) c B s ↔
      wpFold (OpSpec.budget c B) x (fun a s' => IsChargeBound (f a) c B s') s :=
  isChargeBound_bind_iff x f

@[simp]
theorem isChargeBound_map_iff {γ : Type v'} (f : α → γ) (x : FreeM P α) :
    IsChargeBound (FreeM.map f x) c B s ↔ IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih => exact and_congr_right fun _ => forall_congr' fun b => ih b

@[simp]
theorem isChargeBound_map_iff' (f : α → β) (x : FreeM P α) :
    IsChargeBound (f <$> x) c B s ↔ IsChargeBound x c B s :=
  isChargeBound_map_iff f x

@[simp]
theorem isChargeBound_ite (p : Prop) [Decidable p] (x y : FreeM P α) :
    IsChargeBound (if p then x else y) c B s ↔
      if p then IsChargeBound x c B s else IsChargeBound y c B s := by
  split <;> rfl

@[simp]
theorem isChargeBound_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α) :
    IsChargeBound (if h : p then x h else y h) c B s ↔
      if h : p then IsChargeBound (x h) c B s else IsChargeBound (y h) c B s := by
  split <;> rfl

end Bound

section OrderedBound

variable [AddCommMonoid ω] [PartialOrder ω] {c c' : P.A → ω} {B B' s s' : ω}

/-- Starting from less spent keeps a program within budget. -/
theorem IsChargeBound.mono_spent [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (hs : s' ≤ s) :
    IsChargeBound x c B s' := by
  induction x using FreeM.rec generalizing s s' with
  | pure a => exact hs.trans h
  | liftBind a r ih =>
    have hs' : s' + c a ≤ s + c a := add_le_add hs le_rfl
    exact ⟨hs'.trans h.1, fun b => ih b (h.2 b) hs'⟩

/-- A larger budget keeps a program within budget. -/
theorem IsChargeBound.mono {x : FreeM P α} (h : IsChargeBound x c B s) (hB : B ≤ B') :
    IsChargeBound x c B' s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h.trans hB
  | liftBind a r ih => exact ⟨h.1.trans hB, fun b => ih b (h.2 b)⟩

/-- Cheaper calls keep a program within budget. -/
theorem IsChargeBound.mono_charge [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (hc : ∀ a, c' a ≤ c a) : IsChargeBound x c' B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih =>
    have hs : s + c' a ≤ s + c a := add_le_add le_rfl (hc a)
    exact ⟨hs.trans h.1, fun b => (ih b (h.2 b)).mono_spent hs⟩

/-- Shifting the spent amount shifts the budget. -/
theorem IsChargeBound.add_left [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (t : ω) :
    IsChargeBound x c (t + B) (t + s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact add_le_add le_rfl h
  | liftBind a r ih =>
    refine ⟨?_, fun b => ?_⟩
    · rw [add_assoc]; exact add_le_add le_rfl h.1
    · rw [add_assoc]; exact ih b (h.2 b)

/-- **Sequencing.** If `x` stays within `L ≤ B` and each continuation stays within `B` from any
amount at most `L`, then `x >>= f` stays within `B`. -/
theorem IsChargeBound.bind_of_le {γ : Type v'} {x : FreeM P α} {f : α → FreeM P γ} {L : ω}
    (hx : IsChargeBound x c L s) (hL : L ≤ B)
    (hf : ∀ a s', s' ≤ L → IsChargeBound (f a) c B s') :
    IsChargeBound (FreeM.bind x f) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hf a s hx
  | liftBind a r ih =>
    exact ⟨hx.1.trans hL, fun b => ih b (hx.2 b)⟩

end OrderedBound

section CanonicalBound

variable [AddCommMonoid ω] [PartialOrder ω] [CanonicallyOrderedAdd ω]
  {c : P.A → ω} {B B₁ B₂ s : ω}

theorem isChargeBound_pure (a : α) : IsChargeBound (pure a : FreeM P α) c B :=
  zero_le

/-- **Budgets add under sequencing.** -/
theorem IsChargeBound.bind [IsOrderedAddMonoid ω] {γ : Type v'} {x : FreeM P α} {f : α → FreeM P γ}
    (hx : IsChargeBound x c B₁ s) (hf : ∀ a, IsChargeBound (f a) c B₂) :
    IsChargeBound (FreeM.bind x f) c (B₁ + B₂) s := by
  refine hx.bind_of_le le_self_add fun a s' hs' => ?_
  have := (hf a).add_left s'
  rw [add_zero] at this
  exact this.mono (add_le_add hs' le_rfl)

/-- A charge bound in spent-amount form is a roll bound whose budget is the amount spent. -/
theorem isChargeBound_iff_isRollBound (x : FreeM P α) (c : P.A → ω) (B s : ω) :
    IsChargeBound x c B s ↔
      s ≤ B ∧ IsRollBound x s (fun a t => t + c a ≤ B) (fun a t => t + c a) := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isRollBound_liftBind_iff]
    simp only [ih]
    exact ⟨fun h => ⟨le_self_add.trans h.1, h.1, fun b => (h.2 b).2⟩,
      fun h => ⟨h.2.1, fun b => ⟨h.2.1, h.2.2 b⟩⟩⟩

end CanonicalBound

/-! ### Natural-number budgets -/

/-- With natural-number charges, a charge bound is the subtractive roll bound: the remaining
budget `n - s` decreases by `c a` at each call. -/
theorem isChargeBound_iff_isRollBound_tsub (x : FreeM P α) (c : P.A → ℕ) (n s : ℕ) :
    IsChargeBound x c n s ↔
      s ≤ n ∧ IsRollBound x (n - s) (fun a b => c a ≤ b) (fun a b => b - c a) := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isRollBound_liftBind_iff]
    simp only [ih]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨by omega, by omega, fun b => ?_⟩
      rw [show n - s - c a = n - (s + c a) by omega]
      exact (h₂ b).2
    · rintro ⟨_, hc, h₂⟩
      refine ⟨by omega, fun b => ⟨by omega, ?_⟩⟩
      rw [show n - (s + c a) = n - s - c a by omega]
      exact h₂ b

/-- A natural-number charge bound from nothing spent is the subtractive roll bound. -/
theorem isChargeBound_iff_isRollBound_nat (x : FreeM P α) (c : P.A → ℕ) (n : ℕ) :
    IsChargeBound x c n ↔ IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) := by
  simpa using isChargeBound_iff_isRollBound_tsub x c n 0

/-- A unit-charge budget is a total roll bound. -/
theorem isChargeBound_one_iff_isTotalRollBound (x : FreeM P α) (n : ℕ) :
    IsChargeBound x (fun _ => (1 : ℕ)) n ↔ IsTotalRollBound x n := by
  rw [isChargeBound_iff_isRollBound_nat, isTotalRollBound_iff_isRollBound]
  exact isRollBound_congr (fun _ _ => Nat.one_le_iff_ne_zero.trans Nat.pos_iff_ne_zero.symm)
    fun _ _ => rfl

/-! ### Changing the cost type -/

section Transport

variable {ω' : Type w'} [AddCommMonoid ω] [PartialOrder ω] [AddCommMonoid ω'] [PartialOrder ω']
  {c : P.A → ω} {B s : ω}

/-- Charge bounds push forward along monotone additive maps. Indicator, unit and per-kind
charges are pushforwards of one vector charge. -/
theorem IsChargeBound.map {x : FreeM P α} (φ : ω →+o ω') (h : IsChargeBound x c B s) :
    IsChargeBound x (φ ∘ c) (φ B) (φ s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact φ.monotone' h
  | liftBind a r ih =>
    refine ⟨?_, fun b => ?_⟩
    · rw [Function.comp_apply, ← map_add]; exact φ.monotone' h.1
    · rw [Function.comp_apply, ← map_add]; exact ih b (h.2 b)

/-- Charge bounds transfer both ways along additive order embeddings, such as `ℕ ↪ ℕ∞`. -/
theorem isChargeBound_comp_iff {x : FreeM P α} (φ : ω →+ ω') (hφ : ∀ a b, φ a ≤ φ b ↔ a ≤ b) :
    IsChargeBound x (φ ∘ c) (φ B) (φ s) ↔ IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hφ s B
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isChargeBound_liftBind_iff, Function.comp_apply, ← map_add,
      hφ]
    exact and_congr_right fun _ => forall_congr' fun b => ih b

/-- Natural-number budgets as budgets in `ℕ∞`. -/
theorem isChargeBound_natCast_iff {x : FreeM P α} {c : P.A → ℕ} {n s : ℕ} :
    IsChargeBound x (fun a => (c a : ℕ∞)) n s ↔ IsChargeBound x c n s :=
  isChargeBound_comp_iff (Nat.castAddMonoidHom ℕ∞) fun _ _ => Nat.cast_le

end Transport

/-! ### Product and family budgets -/

section Product

variable {ω₁ : Type w} {ω₂ : Type w'} [Add ω₁] [LE ω₁] [Zero ω₁] [Add ω₂] [LE ω₂] [Zero ω₂]

/-- A bound with a pair of charges is a pair of bounds. -/
theorem isChargeBound_prod_iff {x : FreeM P α} {c₁ : P.A → ω₁} {c₂ : P.A → ω₂} {B₁ s₁ : ω₁}
    {B₂ s₂ : ω₂} :
    IsChargeBound x (fun a => (c₁ a, c₂ a)) (B₁, B₂) (s₁, s₂) ↔
      IsChargeBound x c₁ B₁ s₁ ∧ IsChargeBound x c₂ B₂ s₂ := by
  induction x using FreeM.rec generalizing s₁ s₂ with
  | pure a => exact Prod.mk_le_mk
  | liftBind a r ih =>
    simp only [isChargeBound_liftBind_iff, Prod.mk_add_mk, Prod.mk_le_mk, ih]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h⟩
      exact ⟨⟨h₁, fun b => (h b).1⟩, ⟨h₂, fun b => (h b).2⟩⟩
    · rintro ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩⟩
      exact ⟨⟨h₁, h₂⟩, fun b => ⟨h₁' b, h₂' b⟩⟩

/-- A bound with a family of charges is a family of bounds. Per-index query budgets are the
instance with charges `Pi.single i 1`. -/
theorem isChargeBound_pi_iff {ι : Type*} {ω : ι → Type w} [∀ i, Add (ω i)] [∀ i, LE (ω i)]
    [∀ i, Zero (ω i)] {x : FreeM P α} {c : P.A → ∀ i, ω i} {B s : ∀ i, ω i} :
    IsChargeBound x c B s ↔ ∀ i, IsChargeBound x (fun a => c a i) (B i) (s i) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Pi.le_def
  | liftBind a r ih =>
    simp only [isChargeBound_liftBind_iff, Pi.le_def, Pi.add_apply, ih]
    exact ⟨fun h i => ⟨h.1 i, fun b => h.2 b i⟩, fun h => ⟨fun i => (h i).1, fun b i => (h i).2 b⟩⟩

end Product

/-! ### Lenses and free handlers -/

section Transfer

variable {Q : PFunctor.{uA₂, uB₂}} [AddCommMonoid ω] [PartialOrder ω] {B s : ω}

/-- A bound on `x` with the charge pulled back along `l` bounds the relabelled program. -/
theorem IsChargeBound.mapLens (l : Lens P Q) {x : FreeM P α} {c : Q.A → ω}
    (h : IsChargeBound x (c ∘ l.toFunA) B s) : IsChargeBound (x.mapLens l) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, isChargeBound_liftBind_iff]
    exact ⟨h.1, fun d => ih _ (h.2 _)⟩

/-- When every answer of the target is reached by the lens, the bounds agree. -/
theorem isChargeBound_mapLens_iff (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    {x : FreeM P α} {c : Q.A → ω} :
    IsChargeBound (x.mapLens l) c B s ↔ IsChargeBound x (c ∘ l.toFunA) B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, isChargeBound_liftBind_iff, isChargeBound_liftBind_iff]
    refine and_congr_right fun _ => ⟨fun h b => ?_, fun h d => (ih _).2 (h _)⟩
    obtain ⟨d, rfl⟩ := hl a b
    exact (ih _).1 (h d)

end Transfer

section Handler

variable {Q : PFunctor.{uA₂, uB}} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
  {α : Type uB} {B s : ω}

/-- **Free-handler transfer.** If the implementation of each call at `a` stays within `c a` under
the target charge `d`, then simulating a program within `B` under `c` stays within `B` under
`d`. -/
theorem IsChargeBound.liftM (handler : (a : P.A) → FreeM Q (P.B a)) {c : P.A → ω} {d : Q.A → ω}
    (hstep : ∀ a, IsChargeBound (handler a) d (c a)) {x : FreeM P α}
    (hx : IsChargeBound x c B s) : IsChargeBound (x.liftM handler) d B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hx
  | liftBind a r ih =>
    change IsChargeBound (FreeM.bind (handler a) fun b => (r b).liftM handler) d B s
    have hh := (hstep a).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le hx.1 fun b s' hs' => (ih b (hx.2 b)).mono_spent hs'

end Handler


/-! ## Worst-case cost -/

section Cost

variable [AddCommMonoid ω] [CompleteLattice ω] {c c' : P.A → ω}

/-- The worst-case cost of `x` when each leaf `a` costs `k a` in addition to the calls on the way
to it: the fold of `OpSpec.charge c`. -/
noncomputable def costWith (c : P.A → ω) (x : FreeM P α) (k : α → ω) : ω :=
  wpFold (OpSpec.charge c) x k

/-- The worst-case cost of `x`: the largest total charge of the calls along a branch, where a
call at `a` costs `c a`. -/
noncomputable def cost (c : P.A → ω) (x : FreeM P α) : ω :=
  costWith c x fun _ => 0

theorem costWith_eq_wpFold (c : P.A → ω) (x : FreeM P α) (k : α → ω) :
    costWith c x k = wpFold (OpSpec.charge c) x k :=
  rfl

theorem cost_eq_costWith (c : P.A → ω) (x : FreeM P α) : cost c x = costWith c x fun _ => 0 :=
  rfl

@[simp, freeM_unfold]
theorem costWith_pure (a : α) (k : α → ω) : costWith c (pure a : FreeM P α) k = k a :=
  rfl

@[simp, freeM_unfold]
theorem costWith_freeM_pure (a : α) (k : α → ω) : costWith c (FreeM.pure a : FreeM P α) k = k a :=
  rfl

@[freeM_unfold]
theorem costWith_liftBind (a : P.A) (r : P.B a → FreeM P α) (k : α → ω) :
    costWith c (FreeM.liftBind a r) k = c a + ⨆ b, costWith c (r b) k :=
  rfl

@[simp]
theorem costWith_lift (a : P.A) (k : P.B a → ω) :
    costWith (α := no_index (P.B a)) c (FreeM.lift a) k = c a + ⨆ b, k b :=
  rfl

@[simp]
theorem costWith_liftObj (x : P.Obj α) (k : α → ω) :
    costWith c (FreeM.liftObj x) k = c x.1 + ⨆ b, k (x.2 b) :=
  rfl

@[simp]
theorem costWith_bind {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) (k : γ → ω) :
    costWith c (FreeM.bind x f) k = costWith c x fun a => costWith c (f a) k :=
  wpFold_bind' _ x f k

@[simp]
theorem costWith_bind' (x : FreeM P α) (f : α → FreeM P β) (k : β → ω) :
    costWith c (x >>= f) k = costWith c x fun a => costWith c (f a) k :=
  wpFold_bind' _ x f k

@[simp]
theorem costWith_map {γ : Type v'} (f : α → γ) (x : FreeM P α) (k : γ → ω) :
    costWith c (FreeM.map f x) k = costWith c x (k ∘ f) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => exact congrArg (c a + ·) (iSup_congr ih)

@[simp]
theorem costWith_map' (f : α → β) (x : FreeM P α) (k : β → ω) :
    costWith c (f <$> x) k = costWith c x (k ∘ f) :=
  costWith_map f x k

@[simp]
theorem costWith_seq (g : FreeM P (α → β)) (x : FreeM P α) (k : β → ω) :
    costWith c (g <*> x) k = costWith c g fun f => costWith c x (k ∘ f) := by
  rw [seq_eq_bind_map, costWith_bind']
  simp only [costWith_map']

@[simp]
theorem costWith_seqLeft (x : FreeM P α) (y : FreeM P β) (k : α → ω) :
    costWith c (x <* y) k = costWith c x fun a => costWith c y fun _ => k a := by
  simp only [seqLeft_eq_bind, costWith_bind', costWith_pure]

@[simp]
theorem costWith_seqRight (x : FreeM P α) (y : FreeM P β) (k : β → ω) :
    costWith c (x *> y) k = costWith c x fun _ => costWith c y k := by
  rw [seqRight_eq_bind, costWith_bind']

@[simp]
theorem costWith_ite (p : Prop) [Decidable p] (x y : FreeM P α) (k : α → ω) :
    costWith c (if p then x else y) k = if p then costWith c x k else costWith c y k := by
  split <;> rfl

@[simp]
theorem costWith_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α)
    (k : α → ω) :
    costWith c (if h : p then x h else y h) k =
      if h : p then costWith c (x h) k else costWith c (y h) k := by
  split <;> rfl

@[simp, freeM_unfold]
theorem cost_pure (a : α) : cost c (pure a : FreeM P α) = 0 :=
  rfl

@[simp, freeM_unfold]
theorem cost_freeM_pure (a : α) : cost c (FreeM.pure a : FreeM P α) = 0 :=
  rfl

@[freeM_unfold]
theorem cost_liftBind (a : P.A) (r : P.B a → FreeM P α) :
    cost c (FreeM.liftBind a r) = c a + ⨆ b, cost c (r b) :=
  rfl

/-- **Sequencing, exactly**: each leaf of `x` is charged the cost of its continuation. -/
@[simp]
theorem cost_bind {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    cost c (FreeM.bind x f) = costWith c x fun a => cost c (f a) :=
  costWith_bind x f _

@[simp]
theorem cost_bind' (x : FreeM P α) (f : α → FreeM P β) :
    cost c (x >>= f) = costWith c x fun a => cost c (f a) :=
  costWith_bind x f _

@[simp]
theorem cost_map {γ : Type v'} (f : α → γ) (x : FreeM P α) : cost c (FreeM.map f x) = cost c x :=
  costWith_map f x _

@[simp]
theorem cost_map' (f : α → β) (x : FreeM P α) : cost c (f <$> x) = cost c x :=
  costWith_map f x _

@[simp]
theorem cost_ite (p : Prop) [Decidable p] (x y : FreeM P α) :
    cost c (if p then x else y) = if p then cost c x else cost c y := by
  split <;> rfl

@[simp]
theorem cost_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α) :
    cost c (if h : p then x h else y h) = if h : p then cost c (x h) else cost c (y h) := by
  split <;> rfl

section Ordered

variable [IsOrderedAddMonoid ω]

/-- The worst-case cost is monotone in the leaf costs. -/
@[gcongr]
theorem costWith_mono (x : FreeM P α) {k k' : α → ω} (hk : k ≤ k') :
    costWith c x k ≤ costWith c x k' :=
  wpFold_mono (OpSpec.charge_mono c) x hk

/-- The worst-case cost is monotone in the charge. -/
@[gcongr]
theorem costWith_mono_charge (hc : c ≤ c') (x : FreeM P α) (k : α → ω) :
    costWith c x k ≤ costWith c' x k := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih => exact add_le_add (hc a) (iSup_mono ih)

@[gcongr]
theorem cost_mono_charge (hc : c ≤ c') (x : FreeM P α) : cost c x ≤ cost c' x :=
  costWith_mono_charge hc x _

/-- The leaf costs split off: the cost-to-go is at most the cost plus the largest leaf cost. -/
theorem costWith_le_cost_add (x : FreeM P α) (k : α → ω) :
    costWith c x k ≤ cost c x + ⨆ a, k a := by
  induction x using FreeM.rec with
  | pure a => simpa using le_iSup k a
  | liftBind a r ih =>
    rw [costWith_liftBind, cost_liftBind, add_assoc]
    gcongr
    refine iSup_le fun b => (ih b).trans ?_
    gcongr
    exact le_iSup (fun b => cost c (r b)) b

/-- The cost of a sequence is at most the cost of the first part plus the worst continuation. -/
theorem cost_bind_le {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    cost c (FreeM.bind x f) ≤ cost c x + ⨆ a, cost c (f a) := by
  rw [cost_bind]
  exact costWith_le_cost_add x _

end Ordered

section Canonical

variable [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]

omit [IsOrderedAddMonoid ω] in
@[simp]
theorem iSup_zero_eq_zero {ι : Sort*} : (⨆ _ : ι, (0 : ω)) = 0 := by
  rw [← bot_eq_zero, iSup_bot]

omit [IsOrderedAddMonoid ω] in
@[simp]
theorem cost_lift (a : P.A) : cost (α := no_index (P.B a)) c (FreeM.lift a) = c a := by
  change c a + ⨆ _ : P.B a, (0 : ω) = c a
  rw [iSup_zero_eq_zero, add_zero]

omit [IsOrderedAddMonoid ω] in
theorem cost_liftObj (x : P.Obj α) : cost c (FreeM.liftObj x) = c x.1 := by
  change c x.1 + ⨆ _ : P.B x.1, (0 : ω) = c x.1
  rw [iSup_zero_eq_zero, add_zero]

/-- **From the value to the budget.** A bound on the worst-case cost is a structural charge
bound. Together with `cost_le_of_isChargeBound`, this lets `simp` decide budgets by computing
costs. -/
theorem isChargeBound_of_cost_le {x : FreeM P α} {B s : ω} (h : s + cost c x ≤ B) :
    IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rw [cost_liftBind, ← add_assoc] at h
    refine ⟨le_self_add.trans h, fun b => ih b ?_⟩
    exact le_trans (add_le_add le_rfl (le_iSup (fun b => cost c (r b)) b)) h

theorem IsChargeBound.of_cost_le {x : FreeM P α} {B : ω} (h : cost c x ≤ B) :
    IsChargeBound x c B :=
  isChargeBound_of_cost_le (by rwa [zero_add])

omit [IsOrderedAddMonoid ω] in
/-- **From the budget to the value**, where addition distributes over nonempty suprema. -/
theorem cost_le_of_isChargeBound [AddSupDistrib ω] {x : FreeM P α} {B s : ω}
    (h : IsChargeBound x c B s) : s + cost c x ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rw [cost_liftBind, ← add_assoc]
    rcases isEmpty_or_nonempty (P.B a) with hb | hb
    · rw [iSup_of_empty, bot_eq_zero, add_zero]
      exact h.1
    · exact (add_iSup_le_iSup_add _ _).trans (iSup_le fun b => ih b (h.2 b))

theorem isChargeBound_iff_cost_le [AddSupDistrib ω] {x : FreeM P α} {B : ω} :
    IsChargeBound x c B ↔ cost c x ≤ B :=
  ⟨fun h => by simpa using cost_le_of_isChargeBound h, IsChargeBound.of_cost_le⟩

end Canonical

end Cost

/-- A natural-number budget is a bound on the worst-case cost in `ℕ∞`. -/
theorem isChargeBound_iff_cost_natCast_le {x : FreeM P α} {c : P.A → ℕ} {n : ℕ} :
    IsChargeBound x c n ↔ cost (fun a => (c a : ℕ∞)) x ≤ n := by
  rw [← isChargeBound_natCast_iff, Nat.cast_zero, isChargeBound_iff_cost_le]

section CostTransfer

variable [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω]

/-- Relabelling along a lens costs at most the program with the pulled-back charge. -/
theorem costWith_mapLens_le {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) (c : Q.A → ω)
    (x : FreeM P α) (k : α → ω) :
    costWith c (x.mapLens l) k ≤ costWith (c ∘ l.toFunA) x k := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, costWith_liftBind, costWith_liftBind]
    exact add_le_add le_rfl (iSup_le fun d =>
      (ih _).trans (le_iSup (fun b => costWith (c ∘ l.toFunA) (r b) k) _))

theorem cost_mapLens_le {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) (c : Q.A → ω)
    (x : FreeM P α) : cost c (x.mapLens l) ≤ cost (c ∘ l.toFunA) x :=
  costWith_mapLens_le l c x _

omit [IsOrderedAddMonoid ω] in
/-- When every answer of the target is reached by the lens, relabelling preserves the cost. -/
theorem costWith_mapLens_of_surjective {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (hl : ∀ a, Function.Surjective (l.toFunB a)) (c : Q.A → ω) (x : FreeM P α) (k : α → ω) :
    costWith c (x.mapLens l) k = costWith (c ∘ l.toFunA) x k := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, costWith_liftBind, costWith_liftBind]
    congr 1
    exact (hl a).iSup_comp (fun b => costWith (c ∘ l.toFunA) (r b) k) ▸
      iSup_congr fun d => ih _

omit [IsOrderedAddMonoid ω] in
theorem cost_mapLens_of_surjective {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (hl : ∀ a, Function.Surjective (l.toFunB a)) (c : Q.A → ω) (x : FreeM P α) :
    cost c (x.mapLens l) = cost (c ∘ l.toFunA) x :=
  costWith_mapLens_of_surjective l hl c x _

variable {Q : PFunctor.{uA₂, uB}} {α : Type uB}

/-- The worst-case cost of a handler's implementation of the call at `a`. -/
noncomputable def handlerCost (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a)) (a : P.A) :
    ω :=
  cost d (handler a)

/-- **Simulation overhead.** A program simulated through a free handler costs at most the program
with each call charged the worst case of its implementation. -/
theorem costWith_liftM_le (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a))
    (x : FreeM P α) (k : α → ω) :
    costWith d (x.liftM handler) k ≤ costWith (handlerCost d handler) x k := by
  rw [costWith_eq_wpFold, wpFold_liftM]
  induction x using FreeM.rec with
  | pure x => exact le_rfl
  | liftBind a r ih =>
    change costWith d (handler a) (fun u => wpFold _ (r u) k) ≤
      handlerCost d handler a + ⨆ u, costWith (handlerCost d handler) (r u) k
    exact (costWith_le_cost_add (handler a) _).trans (add_le_add le_rfl (iSup_mono ih))

theorem cost_liftM_le (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a)) (x : FreeM P α) :
    cost d (x.liftM handler) ≤ cost (handlerCost d handler) x :=
  costWith_liftM_le d handler x _

end CostTransfer

end FreeM

end PFunctor
