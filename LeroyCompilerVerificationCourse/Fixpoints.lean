import LeroyCompilerVerificationCourse.Imp
import LeroyCompilerVerificationCourse.Constprop
import Batteries.Data.List.Perm

universe u

set_option grind.warning false

@[grind] class OrderStruct (α : Sort u) where
  eq : α → α → Prop
  le : α → α → Prop
  beq : α → α → Bool
  le_trans: ∀ x y z, le x y -> le y z -> le x z
  beq_true' : ∀ x y : α, beq x y = true → eq x y
  beq_false' : ∀ x y : α, beq x y = false → ¬ eq x y
  gt_wf : WellFounded (fun x y : α => le y x ∧ ¬eq y x)
open OrderStruct

@[grind] def gt {α : Sort u} [OrderStruct α] (x y : α) : Prop := le y x ∧ ¬eq y x

def gt_well_founded {α : Sort u} [OrderStruct α] : WellFounded (gt : α → α → Prop) := by apply @gt_wf

class OrderWithBot (α : Sort u) extends OrderStruct α where
  bot : α
  bot_smallest : ∀ x, le bot x

class Monotone (α : Sort u) (F : α → α) [OrderStruct α] where
  F_mon : ∀ {x y : α}, le x y → le (F x) (F y)

open Monotone

section FixpointExistence

variable (α : Sort u) (F : α → α) [OrderWithBot α]

open OrderStruct OrderWithBot
theorem fixpoint_exists_1 [Monotone α F] : ∃ x : α, eq x (F x) := by
  have REC : forall x : α, le x (F x) -> exists y : α , eq y (F y) := by
    intro x
    induction x using @WellFounded.induction α gt gt_wf
    case h x ih =>
      intro h
      by_cases (beq x (F x))
      case pos isTrue =>
        exists x
        grind [beq_true']
      case neg isFalse =>
        apply ih (F x)
        . constructor
          . exact h
          . apply beq_false'
            grind
        . exact F_mon h
  specialize REC
  apply REC
  apply bot_smallest

end FixpointExistence

section Iterate

variable (α : Sort u) [inst : OrderStruct α] (F : α → α) [Monotone α F]

open OrderStruct

instance : WellFoundedRelation α  where
  rel := gt
  wf := gt_wf

@[grind] def iterate (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) : α :=
  if beq x (F x) then x else iterate (F x) (by apply F_mon; exact PRE) (by intro z hyp; specialize SMALL z hyp; apply le_trans; apply F_mon; exact SMALL; exact hyp)
  termination_by x
  decreasing_by
    grind [beq_false']

#check iterate

@[grind] theorem iterate_correct (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) (heq : y = iterate _ F x PRE SMALL ) : eq y (F y) ∧ ∀ z, le (F z) z → le y z := by
  fun_induction iterate
  case case1 x' PRE SMALL isTrue  =>
    constructor
    . rw [←heq] at PRE
      grind [beq_true']
    . intro z hyp
      specialize SMALL z hyp
      grind
  case case2 ih =>
    have := @ih heq
    grind

end Iterate

section Fixpoint
open OrderWithBot
variable {α : Sort u} [i : OrderWithBot α] (F : α → α) [Monotone α F]

@[grind] def fixpoint' : α := iterate α F bot (by apply bot_smallest) (by grind [bot_smallest])

theorem fixpoint_correct :
  eq (fixpoint' F) (F (fixpoint' F)) ∧ ∀ z : α, le (F z) z → le (fixpoint' F) z := by
    unfold fixpoint'
    apply iterate_correct
    rotate_left
    . exact bot
    . apply bot_smallest
    . grind [bot_smallest]
    . rfl
end Fixpoint

section Constprop

open Std.HashMap

@[grind] def Eq' (S1 S2 : Store) : Prop := Equal S1 S2

def Eq'_sym : ∀ S1 S2, Eq' S1 S2 → Eq' S2 S1 := by
  intro S1 S2 hyp
  unfold Eq' Equal at *
  grind [Equiv.symm]

@[grind] theorem Equal_Eq' : ∀ S1 S2, (Equal S1 S2 == true) → Eq' S1 S2 := by grind

@[grind] theorem Equal_nEq : ∀ S1 S2, (Equal S1 S2 == false) → ¬Eq' S1 S2 := by grind

@[grind] theorem Eq_Le : ∀ S1 S2, Eq' S1 S2 → Le S1 S2 := by
  intro S1 S2 heq
  unfold Le
  intro x n heq2
  unfold Eq' Equal  at heq
  simp at *
  grind [Equiv.getElem?_eq]

@[grind] theorem Le_trans : ∀ S1 S2 S3, Le S1 S2 → Le S2 S3 → Le S1 S3 := by grind

@[grind] def Gt (S1 S2 : Store) := Le S2 S1 ∧ ¬ Eq' S2 S1

@[grind] def Increasing (F : Store → Store) := ∀ x y, Le x y → Le (F x) (F y)

theorem hash_set_incl_size_leq (S1 S2 : Store) : Le S2 S1 → List.Subperm (S1.toList) (S2.toList) := by
  intro LE
  unfold Le at LE
  apply List.subperm_of_subset
  . apply List.Pairwise.imp
    rotate_left
    . exact distinct_keys_toList
    . grind
  . intro (k,v) mem
    specialize LE k v (by grind)
    grind

@[grind] theorem Le_cardinal:
  ∀ S T : Store,
  Le T S ->
  S.size <= T.size ∧ (S.size = T.size → Equal S T) := by
    intro S T hyp
    have size_eq : ∀ (S : Store), S.size = S.toList.length := by grind [length_toList]
    rw [size_eq S, size_eq T]
    constructor
    case left =>
      exact List.Subperm.length_le (hash_set_incl_size_leq S T hyp)
    case right =>
      intro eqLen
      unfold Equal
      apply Equiv.of_toList_perm
      apply List.Subperm.perm_of_length_le (hash_set_incl_size_leq S T hyp)
      grind

@[grind] theorem Gt_cardinal:
  forall S S', Gt S S' -> S.size < S'.size := by
    intro S S' hyp
    unfold Gt at hyp
    have ⟨ t₁, t₂ ⟩ := @Le_cardinal S S' (hyp.1)
    apply Nat.lt_of_le_of_ne
    case h₁ => exact t₁
    case h₂ =>
      apply Classical.byContradiction
      intro h
      simp at h
      grind

theorem Gt_wf : WellFounded Gt := by
  have := @InvImage Store Nat Nat.lt fun x => x.size
  have : ∀ (x y : Store), Gt x y → @InvImage Store Nat Nat.lt (fun x => x.size) x y := by
    intro x y heq
    unfold InvImage
    simp
    apply Gt_cardinal
    exact heq
  have subrel : Subrelation Gt (InvImage Nat.lt (fun x : Store => x.size)) := by
    intro x y gt; grind
  apply @Subrelation.wf Store (InvImage Nat.lt (fun x : Store => x.size)) Gt subrel
  exact InvImage.wf (fun x : Store => x.size) (Nat.lt_wfRel.wf)

open OrderStruct

noncomputable instance : OrderStruct Store where
  eq := Equal
  le := Le
  beq (S1 S2 : Store) :=  Decidable.decide (Equal S1 S2)
  le_trans := Le_trans
  beq_true' := by grind
  beq_false' := by grind
  gt_wf := Gt_wf
end Constprop

section FixpointJoin
variable (Init : Store)
variable (F : Store → Store) [Monotone Store F]

instance : Monotone Store (fun x => Join Init (F x)) where
  F_mon := by
    intro x y le
    unfold OrderStruct.le at *
    unfold instOrderStructStore at *
    simp at *
    unfold Le at *
    intro z n isSome
    have ⟨ h1, h2 ⟩:= (Join_characterization Init (F y) z n).1 isSome
    apply (Join_characterization (Init) (F x) z n).2
    constructor
    . exact h1
    . apply @F_mon _ _ _ _ _ y le
      exact h2

noncomputable def fixpoint_join : Store := by
  have := iterate Store (fun x => Join Init (F x)) Init (by apply Le_Join_l)
  apply this
  dsimp
  intro z hyp
  unfold le instOrderStructStore
  dsimp
  unfold Le
  intro x n hyp2
  specialize hyp x n hyp2
  grind

theorem fixpoint_join_eq: Eq' (Join Init (F (fixpoint_join Init F) )) (fixpoint_join Init F) := by
  generalize heq1 : fixpoint_join Init F = t
  apply Eq'_sym
  simp [fixpoint_join] at *
  have := (@iterate_correct Store _ (fun x => Join Init (F x)) _ ?_ ?_ ?_ ?_ ?_ ).1
  unfold Eq'
  . exact this
  . exact Init
  . dsimp
    apply Le_Join_l
  . intro z hyp
    unfold le instOrderStructStore
    dsimp
    unfold Le
    intro x n hyp2
    specialize hyp x n hyp2
    grind
  . rw [heq1]

theorem fixpoint_join_sound : Le Init (fixpoint_join Init F) /\ Le (F (fixpoint_join Init F)) (fixpoint_join Init F) := by
  have LE : Le (Join Init (F (fixpoint_join Init F))) (fixpoint_join Init F) := by
    apply Eq_Le
    apply fixpoint_join_eq
  constructor
  . apply Le_trans
    rotate_left
    . exact LE
    . apply Le_Join_l
  . apply Le_trans
    rotate_left
    . exact LE
    . apply Le_Join_r

theorem fixpoint_join_smallest:
  forall S, Le (Join Init (F S)) S -> Le (fixpoint_join Init F) S := by
    intro S LE
    unfold fixpoint_join
    dsimp
    have := (@iterate_correct Store _ (fun x => Join Init (F x)) _ (fixpoint_join Init F) Init (?_) ?_ ?_).2 S LE
    exact this
    . dsimp
      apply Le_Join_l
    . intro z hyp
      unfold le instOrderStructStore
      dsimp
      unfold Le
      intro x n hyp2
      specialize hyp x n hyp2
      grind
    . unfold fixpoint_join
      dsimp

@[grind] theorem Join_increasing:
  forall S1 S2 S3 S4,
  Le S1 S2 -> Le S3 S4 -> Le (Join S1 S3) (Join S2 S4) := by
    intros
    grind

@[grind] theorem Aeval_increasing: ∀ S1 S2, Le S1 S2 ->
  forall a n, Aeval S2 a = .some n -> Aeval S1 a =.some n := by
    intro S1 S2 LE a
    induction a <;> grind

@[grind] theorem Beval_increasing : ∀ S1 S2, Le S1 S2 ->
  forall b n, Beval S2 b = .some n -> Beval S1 b = .some n := by
    intro S1 S2 LE b
    induction b
    any_goals grind
    case NOT b1 b1_ih =>
      intro n ev
      simp [Beval, lift1] at ev
      grind

theorem Update_increasing:
  forall S1 S2 x a,
  Le S1 S2 ->
  Le (Update x (Aeval S1 a) S1) (Update x (Aeval S2 a) S2) := by
    intros; grind

end FixpointJoin

noncomputable instance wrapper (F : Store → Store) (F_mon : ∀ x y, le x y → le (F x) (F y)) : Monotone Store F where
  F_mon := by grind

noncomputable def fixpoint_join' (S : Store) (F: Store → Store) (F_mon : ∀ x y, le x y → le (F x) (F y)) := by
  have := wrapper F (by grind)
  exact fixpoint_join S F

theorem fixpoint_join_increasing (_ : Store) (F: Store → Store) (F_mon : ∀ x y, le x y → le (F x) (F y)) (S1 S2: Store) : le S1 S2 → le (fixpoint_join' S1 F F_mon) (fixpoint_join' S2 F F_mon) := by
  intro hyp
  apply @fixpoint_join_smallest S1 F (by grind [wrapper]) (fixpoint_join' S2 F F_mon)
  generalize heq : fixpoint_join' S2 F F_mon = fix2
  have : (Le (Join S2 (F fix2)) fix2) := by
    apply Eq_Le
    . have := @fixpoint_join_eq S2 F (by grind [wrapper])
      rw [←heq]
      apply this
  apply Le_trans
  rotate_left
  . apply this
  . apply Join_increasing
    . exact hyp
    . grind

noncomputable def Cexec' : (c : com) →  {F : Store → Store // ∀ x y, le x y → le (F x) (F y)}
| .SKIP => ⟨(fun S => S), by grind⟩
| .ASSIGN x a => ⟨(fun S => Update x (Aeval S a) S), by
      intro x y hyp
      simp
      apply Update_increasing
      . exact hyp ⟩
| .SEQ c1 c2 =>
  let ⟨ f₁, mon₁ ⟩ := Cexec' c1
  let ⟨ f₂, mon₂ ⟩ := Cexec' c2
  ⟨ (fun S => f₂ (f₁ S)), by grind ⟩
| .IFTHENELSE b c1 c2 =>
  let ⟨ f₁, mon₁ ⟩ := Cexec' c1
  let ⟨ f₂, mon₂ ⟩ := Cexec' c2
  ⟨ (fun S =>
    match Beval S b with
    | .some true => f₁ S
    | .some false => f₂ S
    | .none => Join (f₁ S) (f₂ S)
    ), by
      intro x y hyp
      simp
      generalize heq : Beval y b = h
      cases h
      case none =>
        simp [heq]
        apply le_trans
        rotate_right
        . exact Join (f₁ x) (f₂ x)
        rotate_left
        . apply Join_increasing
          . apply mon₁
            . exact hyp
          . apply mon₂
            . exact hyp
        intro id val hyp2
        have := (Join_characterization (f₁ x) (f₂ x) id val).1 hyp2
        split <;> grind
      case some val =>
        have := Beval_increasing x y hyp b val heq
        split <;> grind ⟩
| .WHILE b c1 =>
   let ⟨ f₁, mon₁ ⟩ := Cexec' c1
   ⟨ fun S => fixpoint_join' S f₁ mon₁, by
      simp
      intro x y hyp
      apply fixpoint_join_increasing
      . exact x
      . exact hyp ⟩

noncomputable def Cexec_Constprop (c : com) : Store → Store := (Cexec' c).val
instance (c : com) : Monotone Store (Cexec_Constprop c) where
  F_mon := by
    intro x y hyp
    exact (Cexec' c).property x y hyp
