/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

def infseq {α} (R : α → α → Prop) : α → Prop :=
  λ x : α => ∃ y, R x y ∧ infseq R y
  coinductive_fixpoint

-- Application of the rewrite rule
def infseq_fixpoint {α} (R : α → α → Prop) (x : α) :
    infseq R x = ∃ y, R x y ∧ infseq R y := by
  rw [infseq]

-- The associated coinduction principle
theorem infseq_coinduction_principle {α} (h : α → Prop) (R : α → α → Prop)
    (prem : ∀ (x : α), h x → ∃ y, R x y ∧ h y) : ∀ x, h x → infseq R x := by
  apply infseq.coinduct
  grind

/--
info: infseq.coinduct.{u_1} {α : Sort u_1} (R : α → α → Prop) (pred : α → Prop)
  (hyp : ∀ (x : α), pred x → ∃ y, R x y ∧ pred y) (x✝ : α) : pred x✝ → infseq R x✝
-/
#guard_msgs in #check infseq.coinduct

-- Simple proof by coinduction
theorem cycle_infseq {R : α → α → Prop} (x : α) : R x x → infseq R x :=
  infseq.coinduct R (λ m => R m m) (by grind) _

@[grind] inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ {x y z}, R x y → star R y z → star R x z

-- Whenever we have `star R y z` and want to prove `star R x z`, look for `R x y`:
attribute [grind =>] star.star_step

@[grind] theorem star_one (R : α → α → Prop) {a b : α} (h : R a b) : star R a b :=
  star.star_step h (by grind)

@[grind] theorem star_trans {α} (R : α → α → Prop) (a b : α) (sab : star R a b) : ∀ c : α, star R b c → star R a c := by
  induction sab with grind

@[grind cases]
inductive plus (R : α → α → Prop) : α → α → Prop where
| plus_left : ∀ {a b c}, R a b → star R b c → plus R a c

-- Whenever we have `star R b c` and want to prove `plus R a c`, look for `R a b`:
grind_pattern plus.plus_left => star R b c, plus R a c

@[grind ←]
theorem plus_one {a b} (h : R a b) : plus R a b :=
  plus.plus_left h (by grind)

@[grind] theorem plus_star {a b} (h : plus R a b) : star R a b := by
    grind

@[grind] theorem plus_star_trans (R : α → α → Prop) : ∀ (a b c : α), star R a b → plus R b c → plus R a c := by
  intro a b c s p
  induction s
  case star_refl => grind
  case star_step d e f rel s2 ih =>
    apply plus.plus_left
    exact rel
    grind

theorem star_plus_trans :
  ∀ a b c, star R a b -> plus R b c -> plus R a c := by
    intro a b c H0 H1
    cases H0
    case star_refl =>
      grind
    case star_step y a1 a2 =>
      apply plus.plus_left
      · exact a1
      · grind

-- grind_pattern star_plus_trans => star R a b, plus R b c

theorem plus_right : star R a b -> R b c -> plus R a c := by grind

def all_seq_inf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, star R x y → ∃ z, R y z

def infseq_with_function (R : α → α → Prop) (a: α) : Prop :=
  ∃ f : Nat → α, f 0 = a ∧ ∀ i, R (f i) (f (1 + i))

def infseq_if_all_seq_inf (R : α → α → Prop) : ∀ x, all_seq_inf R x → infseq R x := by
  apply infseq.coinduct
  intro x H
  apply Exists.elim (H x (by grind))
  intro y Rxy
  exists y
  constructor
  · exact Rxy
  · intro y' Ryy'
    unfold all_seq_inf at H
    apply H
    grind

theorem infseq_coinduction_principle_2
    (X : α → Prop) (h₁ : ∀ (a : α), X a → ∃ b, plus R a b ∧ X b) (a : α) (rel : X a) : infseq R a := by
  apply infseq.coinduct _ (fun a => ∃ b, star R a b ∧ X b) <;> grind

theorem infseq_from_function : ∀ a, infseq_with_function R a → infseq R a := by
  apply infseq.coinduct
  intro x hyp
  unfold infseq_with_function at hyp
  have ⟨f , ⟨h0, hsucc⟩⟩ := hyp
  refine ⟨f 1, by grind, ?_⟩
  unfold infseq_with_function
  refine ⟨fun n => f (n + 1), by grind⟩

@[grind] def irred (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬(R a b)

theorem star_star_inv (R_functional : ∀ a b c, R a b -> R a c -> b = c) (sab : star R a b) :
    ∀ c, star R a c → star R b c ∨ star R c b := by
  induction sab with grind

theorem finseq_unique (R_functional : ∀ a b c, R a b -> R a c -> b = c) :
  ∀ a b b', star R a b → irred R b → star R a b' → irred R b' → b = b' := by
    intro a b b' sab ib sab' ib'
    apply Or.elim (star_star_inv R_functional sab b' sab') <;> grind

@[grind] theorem infseq_star_inv (R_functional : ∀ a b c, R a b -> R a c -> b = c) : ∀ a b, star R a b → infseq R a → infseq R b := by
  intro a b sab ia
  induction sab with grind [infseq]

theorem infseq_finseq_excl (R_functional : ∀ a b c, R a b -> R a c -> b = c): ∀ a b, star R a b → irred R b → infseq R a → False := by
  intro a b sab irb ia
  have h : infseq R b := by grind
  grind [infseq]

theorem infseq_all_seq_inf (R_functional : ∀ a b c, R a b -> R a c -> b = c): ∀ a, infseq R a → all_seq_inf R a := by
  intro a ia
  unfold all_seq_inf
  intro b sab
  have h : infseq R b := by grind
  grind [infseq]
