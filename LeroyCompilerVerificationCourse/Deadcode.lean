import LeroyCompilerVerificationCourse.Imp
import Std.Data.HashSet
set_option grind.warning false
open Classical in

@[grind] def IdentSet := Std.HashSet ident
  deriving Membership, Union, EmptyCollection

@[grind] instance : HasSubset IdentSet where
  Subset (a b : IdentSet) := ∀ x ∈ a, x ∈ b

@[grind] noncomputable instance (a b : IdentSet) : Decidable (a ⊆ b) := Classical.propDecidable (a ⊆ b)

@[grind] instance (x : ident) (a: IdentSet) : Decidable (x ∈ a) := Std.HashSet.instDecidableMem

@[grind] instance : EmptyCollection IdentSet where
  emptyCollection := Std.HashSet.emptyWithCapacity

@[grind] axiom union_characterisation (a b : IdentSet) (x : ident) : x ∈ (a ∪ b) ↔ x ∈ a ∨ x ∈ b

@[grind] theorem union_characterisation2 (a b c : IdentSet) : a ⊆ b ∧ a ⊆ c → a ⊆ (b ∪ c) := by
  intro ⟨ m1 , m2 ⟩
  intro y mem
  specialize m1 y mem
  specialize m2 y mem
  grind


@[grind] theorem insert_characterisation (a : IdentSet) (x : ident) : x ∈ a.insert x := by
  grind [Std.HashSet.contains_insert]

@[grind] def fv_aexp (a: aexp) : IdentSet :=
  match a with
  | .CONST _ => ∅
  | .VAR v => Std.HashSet.instSingleton.singleton v
  | .PLUS a1 a2 =>  (fv_aexp a1) ∪ (fv_aexp a2)
  | .MINUS a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)

@[grind] def fv_bexp (b: bexp) : IdentSet :=
  match b with
  | .TRUE => ∅
  | .FALSE => ∅
  | .EQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .LESSEQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .NOT b1 => fv_bexp b1
  | .AND b1 b2 => (fv_bexp b1) ∪ (fv_bexp b2)

@[grind] def fv_com (c: com) : IdentSet :=
  match c with
  | .SKIP => ∅
  | .ASSIGN _ a => fv_aexp a
  | .SEQ c1 c2 => (fv_com c1) ∪ (fv_com c2)
  | .IFTHENELSE b c1 c2 => (fv_bexp b) ∪ ((fv_com c1) ∪ (fv_com c2))
  | .WHILE b c => (fv_bexp b) ∪ (fv_com c)

@[grind] noncomputable def deadcode_fixpoint_rec (F : IdentSet → IdentSet) (default : IdentSet) (fuel: Nat) (x: IdentSet) : IdentSet :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
      let x' := F x
      if x' ⊆ x then x else deadcode_fixpoint_rec F default fuel x'

@[grind] noncomputable def deadcode_fixpoint (F : IdentSet → IdentSet) (default : IdentSet): IdentSet :=
  deadcode_fixpoint_rec F default 20 ∅

@[grind] theorem  fixpoint_charact' (n : Nat) (x : IdentSet)  (F : IdentSet → IdentSet) (default : IdentSet):
  ((F (deadcode_fixpoint_rec F default n x)) ⊆ (deadcode_fixpoint_rec F default n x)) ∨ (deadcode_fixpoint_rec F default n x = default) := by
    induction n generalizing x <;> grind

theorem fixpoint_charact (F : IdentSet → IdentSet) (default : IdentSet) :
    ((F (deadcode_fixpoint F default)) ⊆ (deadcode_fixpoint F default)) ∨ (deadcode_fixpoint F default = default) := by grind

theorem fixpoint_upper_bound (F : IdentSet → IdentSet) (default : IdentSet) (F_stable : ∀ x , x ⊆ default -> (F x) ⊆ default): deadcode_fixpoint F default ⊆ default := by
  have : ∀ n : Nat, ∀ x : IdentSet, x ⊆ default → (deadcode_fixpoint_rec F default n x) ⊆ default := by
    intro n
    induction n
    case zero =>
      intro x contained
      simp [deadcode_fixpoint_rec]
      unfold Subset
      unfold instHasSubsetIdentSet
      grind
    case succ n ih =>
      unfold deadcode_fixpoint_rec
      simp
      intro x hyp
      split
      case isTrue => grind
      case isFalse => grind
  apply this
  unfold Subset
  unfold instHasSubsetIdentSet
  grind

@[grind] noncomputable def live (c: com) (L: IdentSet) : IdentSet :=
  match c with
  | .SKIP => L
  | .ASSIGN x a =>
      if x ∈ L
      then (L.erase x) ∪ (fv_aexp a)
      else L
  | .SEQ c1 c2 =>
      live c1 (live c2 L)
  | .IFTHENELSE b c1 c2 =>
       (fv_bexp b) ∪ ((live c1 L) ∪ (live c2 L))
  | .WHILE b c =>
      let L' := (fv_bexp b) ∪  L
      let default := (fv_com (.WHILE b c)) ∪ L
      deadcode_fixpoint (fun x => L' ∪ (live c x)) default

theorem live_upper_bound:
  forall c L,
   (live c L) ⊆ ((fv_com c) ∪  L) := by
    intro c
    induction c
    case SKIP =>
      intro L
      simp [fv_com, live]
      unfold Subset
      unfold instHasSubsetIdentSet
      grind
    case ASSIGN x a =>
      intro L
      simp [fv_com, live]
      split
      case isTrue h =>
        unfold Subset
        unfold instHasSubsetIdentSet
        grind
      case isFalse h =>
        unfold Subset
        unfold instHasSubsetIdentSet
        grind
    case SEQ c1 c2 c1_ih c2_ih =>
      intro L
      simp [live, fv_com]
      unfold Subset at *
      unfold instHasSubsetIdentSet at *
      simp at *
      intro x contained
      specialize c1_ih (live c2 L) x contained
      grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      unfold Subset at *
      unfold instHasSubsetIdentSet at *
      simp at *
      grind
    case WHILE b c1 c1_ih =>
      simp [live, fv_com]
      intro L
      apply fixpoint_upper_bound
      intro x hyp
      intro y hyp2
      have : y ∈ fv_bexp b ∨ y ∈ L ∨ y ∈ live c1 x := by grind
      apply Or.elim this
      next =>
        intro hyp3
        grind
      next =>
        intro hyp3
        apply Or.elim hyp3
        next => grind
        next =>
          clear hyp3
          intro hyp3
          specialize c1_ih x y hyp3
          have : y ∈ fv_com c1 ∨ y ∈ x := by grind
          apply Or.elim this
          next => intros; grind
          next =>
            intro hyp4
            specialize hyp y hyp4
            grind

theorem live_while_charact (b : bexp) (c : com) (L L' : IdentSet)
  (eq : L' = live (.WHILE b c) L) :
  (fv_bexp b) ⊆ L' ∧ L ⊆ L' ∧ (live c L') ⊆ L' := by
    have hyp := fixpoint_charact (fun x : IdentSet => (fv_bexp b) ∪ L ∪ (live c x)) ((fv_bexp b) ∪ (fv_com c) ∪ L)
    apply Or.elim hyp
    case left =>
      intro included
      constructor
      case left =>
        intro y contained
        specialize included y (by grind)
        grind
      case right =>
        constructor
        case left =>
          intro y mem
          specialize included y (by grind)
          grind
        case right =>
          intro y mem
          rw [eq]
          specialize included y (by grind)
          grind
    case right =>
      intro equal
      constructor
      case left =>
        intro y mem
        grind
      case right =>
        constructor
        case left =>
          intro y mem
          grind
        case right =>
          intro y mem
          have := live_upper_bound c L' y mem
          grind

@[grind] noncomputable def dce (c: com) (L: IdentSet): com :=
  match c with
  | .SKIP => .SKIP
  | .ASSIGN x a => if x ∈ L then .ASSIGN x a else .SKIP
  | .SEQ c1 c2 => .SEQ (dce c1 (live c2 L)) (dce c2 L)
  | .IFTHENELSE b c1 c2 => .IFTHENELSE b (dce c1 L) (dce c2 L)
  | .WHILE b c => .WHILE b (dce c (live (.WHILE b c) L))

@[grind] def agree (L: IdentSet) (s1 s2: store) : Prop :=
  forall x, x  ∈ L -> s1 x = s2 x

@[grind] theorem agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> L ⊆ L' -> agree L s1 s2 := by
    intro L L' s1 s2 AG sub
    unfold agree at *
    intro x inL
    specialize sub x inL
    specialize AG x sub
    exact AG

@[grind] theorem aeval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall a, (fv_aexp a) ⊆ L -> aeval s1 a = aeval s2 a := by
    intro L s1 s2 AG a
    induction a
    any_goals grind
    case VAR x =>
      simp [fv_aexp]
      intro mem
      have : x ∈ L := by
        have := insert_characterisation ∅ x
        specialize mem x this
        exact mem
      simp [aeval]
      unfold agree at AG
      specialize AG x this
      exact AG
    case PLUS a1 a2 a1_ih a2_ih =>
      intro contained
      simp [aeval]
      congr 1
      next =>
        apply a1_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
      next =>
        apply a2_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
    case MINUS a1 a2 a1_ih a2_ih =>
      intro contained
      simp [aeval]
      congr 1
      next =>
        apply a1_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
      next =>
        apply a2_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained

theorem beval_agree:
  ∀ L s1 s2, agree L s1 s2 ->
  forall b, (fv_bexp b) ⊆ L -> beval s1 b = beval s2 b := by
    intro L s1 s2 AG b
    induction b
    any_goals grind
    case EQUAL a1 a2 =>
      intro cont
      unfold agree at AG
      simp [fv_bexp] at cont
      have aeval_lemma := aeval_agree L s1 s2 AG
      have subgoal1 : fv_aexp a1 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have subgoal2 : fv_aexp a2 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have eq1 := aeval_lemma a1 subgoal1
      have eq2 := aeval_lemma a2 subgoal2
      grind
    case LESSEQUAL a1 a2 =>
      intro cont
      unfold agree at AG
      simp [fv_bexp] at cont
      have aeval_lemma := aeval_agree L s1 s2 AG
      have subgoal1 : fv_aexp a1 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have subgoal2 : fv_aexp a2 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have eq1 := aeval_lemma a1 subgoal1
      have eq2 := aeval_lemma a2 subgoal2
      grind
    case AND b1 b2 b1_ih b2_ih =>
      intro cont
      simp [fv_bexp] at cont
      have : fv_bexp b1 ⊆ L ∧ fv_bexp b2 ⊆ L := by
        constructor
        case left =>
          intro y mem
          specialize cont y (by grind)
          exact cont
        case right =>
          intro y mem
          specialize cont y (by grind)
          exact cont
      specialize b1_ih (by grind)
      specialize b2_ih (by grind)
      grind

theorem agree_update_live:
  forall s1 s2 L x v,
  agree (L.erase x) s1 s2 ->
  agree L (update x v s1) (update x v s2) := by
    intro s1 s2 L x v AG
    unfold agree at *
    intro y
    specialize AG y
    intro inL
    by_cases x = y
    case neg notEq =>
      specialize AG (by grind)
      grind
    case pos isEq =>
      grind

theorem agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ¬x ∈ L ->
  agree L (update x v s1) s2 := by
    intro s1 s2 L x v AG not
    unfold agree at *
    intro y mem
    specialize AG y mem
    simp [update]
    by_cases x=y <;> grind

theorem dce_correct_terminating:
  forall s c s', cexec s c s' ->
  forall L s1, agree (live c L) s s1 ->
  exists s1', cexec s1 (dce c L) s1' /\ agree L s' s1' := by
    intro s c s' EXEC
    induction EXEC
    any_goals grind
    case cexec_while_loop s1 b c1 s2 s3 isTrue EX1 EX2 a_ih a_ih2 =>
      intro L s4 hyp
      have := live_while_charact b c1 L  (live (com.WHILE b c1) L) (by grind)
      have : agree (live c1 (live (com.WHILE b c1) L)) s1 s4 := by
        apply agree_mon
        . exact hyp
        . grind
      have ⟨ t1, ht1, ht2⟩ :=  a_ih (live (.WHILE b c1) L) s4 this
      have ⟨u1, hu1, hu2 ⟩ :=  a_ih2 L t1 ht2
      exists u1
      constructor
      rotate_right
      . exact hu2
      . apply cexec.cexec_while_loop
        . have := beval_agree (live (com.WHILE b c1) L) s1 s4 hyp b (by grind)
          grind
        . exact ht1
        . grind
    case cexec_assign s2 x a=>
      intro L s3 AG
      simp [live] at AG
      by_cases x ∈ L
      case neg notIn =>
        exists s3
        constructor
        . grind [dce]
        . simp [notIn] at AG
          exact @agree_update_dead s2 s3 L x (aeval s2 a) (by grind) notIn
      case pos isIn =>
        simp [isIn] at AG
        exists (update x (aeval s3 a) s3)
        constructor
        . simp [dce, isIn]
          grind
        . have subgoal : aeval s2 a = aeval s3 a := by
            apply aeval_agree
            . exact AG
            . intro y mem
              grind
          rw [subgoal]
          apply @agree_update_live
          grind
    case cexec_ifthenelse s2 b c1 c2 s3 EXEC ih =>
      intro L s4 AG
      simp [dce]
      have EQ : beval s2 b = beval s4 b := by
        apply beval_agree
        . apply AG
        . simp [live]
          intro y mem
          grind
      by_cases beval s2 b = true
      case pos isTrue =>
        simp [isTrue] at EXEC
        specialize ih L s4
        simp [live] at AG
        simp [isTrue] at ih
        have ⟨s5 , EX', AG' ⟩ := ih (by grind)
        exists s5
        constructor
        . apply cexec.cexec_ifthenelse
          grind
        . exact AG'
      case neg isFalse =>
        simp [isFalse] at EXEC
        specialize ih L s4
        simp [live] at AG
        simp [isFalse] at ih
        have ⟨s5 , EX', AG' ⟩ := ih (by grind)
        exists s5
        constructor
        . apply cexec.cexec_ifthenelse
          grind
        . exact AG'
    case cexec_while_done s2 b c isFalse =>
      intro L s1 AG
      have ⟨ h1 , h2 , h3 ⟩ := live_while_charact b c L (live (com.WHILE b c) L) (by grind)
      have EQ : beval s2 b = beval s1 b := by
        apply beval_agree
        . apply AG
        . intro y mem
          specialize h1 y mem
          exact h1
      exists s1
      grind
