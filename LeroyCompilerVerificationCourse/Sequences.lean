/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

/-
  Finite sequences of transitions

  Zero, one or several transitions: reflexive, transitive closure of `R`.
-/
@[grind] inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ {x y z}, R x y → star R y z → star R x z

-- Whenever we have `star R y z` and want to prove `star R x z`, look for `R x y`:
attribute [grind =>] star.star_step

@[grind] theorem star_one (R : α → α → Prop) {a b : α} (h : R a b) : star R a b :=
  star.star_step h (by grind)

@[grind] theorem star_trans {α} (R : α → α → Prop) (a b : α) (sab : star R a b) : ∀ c : α, star R b c → star R a c := by
  induction sab with grind

/-
  One or several transitions: transitive closure of `R`.
-/
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

/-
  No transitions from a state.
-/
@[grind] def irred (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬(R a b)

/-
  Infinite sequences of transitions

  It is easy to characterize the fact that all transition sequences starting
  from a state `a` are infinite: it suffices to say that any finite sequence
  starting from `a` can always be extended by one more transition.
-/
def all_seq_inf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, star R x y → ∃ z, R y z

/-
  However, this is not the notion we are trying to characterize: that, starting
  from `x`, there exists one infinite sequence of transitions
  `x` --> `x₁` --> `x₂` --> ... -> `xₙ` -> ....

  Indeed, consider `R : Nat → Nat → Prop` such that `R 0 0` and `R 0 1`.
  `all_seq_inf 0` does not hold, because a sequence `0` -->* `1` cannot be extended.
  Yet, `R` admits an infinite sequence, namely `0` --> `0` --> ...

  Another attempt would be to represent the sequence of states
  `x` --> `x₁` --> `x₂` --> ... -> `xₙ` -> ... explicitly, as a function
  `f : Nat → α` such that `f i` is the `i`-th state `xᵢ` of the sequence.
-/
def infseq_with_function (R : α → α → Prop) (a: α) : Prop :=
  ∃ f : Nat → α, f 0 = a ∧ ∀ i, R (f i) (f (1 + i))
/-
  This is a correct characterization of the existence of an infinite sequence
  of reductions.  However, it is very inconvenient to work with this definition.

  To obtain a practical definition of infinite sequences, we use the following
  coinductive definition of the predicate `infseq R`.

  An inductive predicate is the least fixpoint: the smallest predicate that satisfies its constructors; a coinductive predicate is a greatest fixpoint: the largest predicate that satisfies its defining equation.

  The `infseq` predicate above must be defined coinductively.  Indeed, if we define it inductively, the predicate would be empty (always false), since there are no base cases!
-/
def infseq {α} (R : α → α → Prop) : α → Prop :=
  λ x : α => ∃ y, R x y ∧ infseq R y
  coinductive_fixpoint

-- Application of the rewrite rule
def infseq_fixpoint {α} (R : α → α → Prop) (x : α) :
    infseq R x = ∃ y, R x y ∧ infseq R y := by
  rw [infseq]

/-
Consider a set `h` of states `α`, that is, a predicate `h : α → Prop.

Assume that for every `x` in `h`, we can make one `R` transition to a `y`
that is still in `h`.  Then, starting from `x` in `h`, we can transition to
some `x₁` in `h`, then to some `x₂` still in `h`, then... It is clear
that we are just building an infinite sequence of transitions starting from
`x`. Therefore `infseq R x` should hold.
-/
theorem infseq_coinduction_principle {α} (h : α → Prop) (R : α → α → Prop)
    (prem : ∀ (x : α), h x → ∃ y, R x y ∧ h y) : ∀ x, h x → infseq R x := by
  apply infseq.coinduct
  grind

/-
  Lean provides support for constructing proofs by coinduction.
  For example, we can prove the following:
-/

theorem cycle_infseq {R : α → α → Prop} (x : α) : R x x → infseq R x :=
  infseq.coinduct R (λ m => R m m) (by grind) _

/-
  An even more useful variant of this coinduction principle considers a
  set `X` where for every `a` in `X`, we can make one *or several* transitions
  to reach a `b` in `X`.
-/
theorem infseq_coinduction_principle_2
    (X : α → Prop) (h₁ : ∀ (a : α), X a → ∃ b, plus R a b ∧ X b) (a : α) (rel : X a) : infseq R a := by
  apply infseq.coinduct _ (fun a => ∃ b, star R a b ∧ X b) <;> grind

/-
  Here is an example of use of `infseq_coinduction_principle`:
  if all finite transition sequences starting at `x` can be extended,
  `infseq R x` holds.
-/
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

/-
  Likewise, the function-based characterization `infseq_with_function`
  implies `infseq`.
-/
theorem infseq_from_function : ∀ a, infseq_with_function R a → infseq R a := by
  apply infseq.coinduct
  intro x hyp
  unfold infseq_with_function at hyp
  have ⟨f , ⟨h0, hsucc⟩⟩ := hyp
  refine ⟨f 1, by grind, ?_⟩
  unfold infseq_with_function
  refine ⟨fun n => f (n + 1), by grind⟩

section

/-
  A transition relation is functional if every state can transition to at most
  one other state.
-/
variable {R : α → α → Prop} (R_functional : ∀ a b c, R a b -> R a c -> b = c)

include R_functional

/-
  Uniqueness of finite transition sequences.
-/
theorem star_star_inv (sab : star R a b) :
    ∀ c, star R a c → star R b c ∨ star R c b := by
  induction sab with grind

theorem finseq_unique :
  ∀ a b b', star R a b → irred R b → star R a b' → irred R b' → b = b' := by
    intro a b b' sab ib sab' ib'
    apply Or.elim (star_star_inv R_functional sab b' sab') <;> grind

/-
  A state cannot both diverge and terminate on an irreducible state.
-/
@[grind] theorem infseq_star_inv  : ∀ a b, star R a b → infseq R a → infseq R b := by
  intro a b sab ia
  induction sab with grind [infseq]

theorem infseq_finseq_excl : ∀ a b, star R a b → irred R b → infseq R a → False := by
  intro a b sab irb ia
  have h : infseq R b := by grind
  grind [infseq]

/-
  If there exists an infinite sequence of transitions from `a`,
  all sequences of transitions arising from `a` are infinite.
-/
theorem infseq_all_seq_inf : ∀ a, infseq R a → all_seq_inf R a := by
  intro a ia
  unfold all_seq_inf
  intro b sab
  have h : infseq R b := by grind
  grind [infseq]

end
