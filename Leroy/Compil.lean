import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic

set_option grind.warning false

@[grind] inductive instr : Type where
  | Iconst (n: Int)
  | Ivar (x: ident)
  | Isetvar (x: ident)
  | Iadd
  | Iopp
  | Ibranch (d: Int)
  | Ibeq (d1: Int) (d0: Int)
  | Ible (d1: Int) (d0: Int)
  | Ihalt
    deriving Repr

@[grind] def codelen (c: List instr) : Int := c.length

def stack : Type := List Int

def config : Type := Int × stack × store

@[grind] def instr_at (C : List instr) (pc : Int) : Option instr :=
  match C with
  | [] => .none
  | i :: C' => if pc = 0 then .some i else instr_at C' (pc - 1)

@[grind] inductive transition (C: List instr): config → config → Prop where
  | trans_const : ∀ pc stk s n,
      instr_at C pc = .some (.Iconst n) →
      transition C (pc    , stk     , s)
                   (pc + 1, n :: stk, s)
  | trans_var : forall pc stk s x,
      instr_at C pc = .some (.Ivar x) ->
      transition C (pc    , stk       , s)
                   (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
      instr_at C pc = .some (.Isetvar x) ->
      transition C (pc    , n :: stk, s)
                   (pc + 1, stk     , update x n s)
  | trans_add: forall pc stk s n1 n2,
      instr_at C pc = .some (.Iadd) ->
      transition C (pc    , n2 :: n1 :: stk , s)
                   (pc + 1, (n1 + n2) :: stk, s)
  | trans_opp: forall pc stk s n,
      instr_at C pc = .some (.Iopp) ->
      transition C (pc    , n :: stk    , s)
                   (pc + 1, (- n) :: stk, s)
  | trans_branch: forall pc stk s d pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , stk, s)
                   (pc', stk, s)
  | trans_beq: forall pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 = n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)
  | trans_ble: forall pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ible d1 d0) ->
      pc' = pc + 1 + (if n1 ≤ n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)

def transitions (C: List instr) : config -> config -> Prop :=
  star (transition C)

def machine_terminates (C: List instr) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

def machine_goes_wrong (C: List instr) (s_init: store) : Prop :=
  exists pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

@[grind ]def compile_aexp (a: aexp) : List instr :=
  match a with
  | .CONST n => .Iconst n :: []
  | .VAR x => .Ivar x :: []
  | .PLUS a1 a2  => (compile_aexp a1) ++ (compile_aexp a2) ++ (.Iadd :: [])
  | .MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ (.Iopp :: .Iadd :: [])

def compile_bexp (b: bexp) (d1: Int) (d0: Int) : List instr :=
  match b with
  | .TRUE => if d1 = 0 then [] else .Ibranch d1 :: []
  | .FALSE => if d0 = 0 then [] else .Ibranch d0 :: []
  | .EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ibeq d1 d0 :: []
  | .LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ible d1 d0 :: []
  | .NOT b1 => compile_bexp b1 d0 d1
  | .AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0
      let code1 := compile_bexp b1 0 (codelen code2 + d0)
      code1 ++ code2

def compile_com (c: com) : List instr:=
  match c with
  | .SKIP =>
      []
  | .ASSIGN x a =>
      compile_aexp a ++ .Isetvar x :: []
  | .SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | .IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso
      let code_ifnot := compile_com ifnot
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ .Ibranch (codelen code_ifnot)
      :: code_ifnot
  | .WHILE b body =>
      let code_body := compile_com body
      let code_test := compile_bexp b 0 (codelen code_body + 1)
      code_test
      ++ code_body
      ++ .Ibranch (- (codelen code_test + codelen code_body + 1)) :: []

def compile_program (p: com) : List instr:=
  compile_com p ++ .Ihalt :: []

#eval (compile_program (.ASSIGN "x" (.PLUS (.VAR "x") (.CONST 1))))

def smart_Ibranch (d: Int) : List instr:=
  if d = 0 then [] else .Ibranch d :: []

@[grind] inductive code_at: List instr -> Int -> List instr-> Prop where
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2

@[grind] theorem codelen_cons:
  forall i c, codelen (i :: c) = codelen c + 1 := by grind

@[grind] theorem codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 c2
    induction c1
    all_goals grind

@[grind =>] theorem instr_a : forall i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1.append (i :: c2) ) pc = .some i := by
    intro i c2 c1 pc
    induction c1 generalizing pc
    case nil =>
      dsimp [instr_at, codelen]
      grind
    case cons h t ih =>
      dsimp [codelen, instr_at]
      intro h1
      split
      all_goals grind [List.append_eq]

@[grind] theorem instr_at_app:
  ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1.append (i :: c2)) pc = .some i := by
    intro i c2 c1 pc pc_eq
    induction c1 generalizing pc
    case nil =>
      dsimp [instr_at]
      dsimp [codelen] at pc_eq
      grind
    case cons h t t_ih =>
      grind [instr_at, codelen, List.append_eq]

theorem code_at_head :
  forall C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = .some i := by
    intro C pc i C'  H
    generalize heq1 : (i :: C') = x
    rw [heq1] at H
    induction H
    case code_at_intro c1 c2 c3 oc a =>
      unfold instr_at
      rw [←heq1]
      induction c1 generalizing oc
      case nil =>
        grind
      case cons h t t_ih =>
        have _ : oc ≠ 0 := by grind
        have _ : t ++ i :: (C' ++ c3) ≠ [] := by grind
        dsimp
        grind

@[grind] theorem code_at_tail :
   forall C pc i C',
  code_at C pc (i :: C') →
  code_at C (pc + 1) C' := by
    intro C pc i C' h
    cases h
    case code_at_intro c1 c3 a =>
      have s : c1 ++ i :: C' ++ c3 = c1 ++ [i] ++ C' ++ c3 := by grind [List.append_cons]
      rw [s]
      apply code_at.code_at_intro
      grind

@[grind] theorem code_at_app_left:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1 := by
    intro c pc m1 m2 h
    cases h
    case code_at_intro c1 c3 a =>
      have := code_at.code_at_intro c1 m1 (m2 ++ c3) pc a
      grind [List.append_assoc]

@[grind] theorem code_at_app_right:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 e (pc + codelen c1) (by grind)
      grind [List.append_assoc]

@[grind] theorem code_at_app_right2 : forall C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) →
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 c3 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 (c3 ++ e) (pc + codelen c1) (by grind)
      grind [List.append_assoc]

@[grind] theorem code_at_nil : forall C pc C1,
  code_at C pc C1 -> code_at C pc [] := by
    intro C pc c1 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro b [] (c1 ++ e) pc a
      grind [List.append_nil, List.append_assoc]

@[grind] theorem instr_at_code_at_nil :
  forall C pc i, instr_at C pc = .some i -> code_at C pc [] := by
    intro C pc i h
    induction C generalizing pc i
    case nil => grind
    case cons f t t_ih =>
      unfold instr_at at h
      by_cases pc = 0
      rotate_left
      next nz =>
        simp [nz] at h
        specialize t_ih (pc - 1) i h
        cases t_ih
        next c1 c3 a =>
          simp
          have := code_at.code_at_intro (f :: c1) [] c3 pc
          grind
      next z =>
        have := code_at.code_at_intro [] [] (f :: t) pc
        grind [List.nil_append]

@[grind] theorem code_at_to_instr_at : code_at C pc (c1 ++ i :: c2) → instr_at C (pc + codelen c1) = .some i := by
    intro h
    cases h
    next b e a =>
      have := instr_at_app i (c2 ++ e) (b ++ c1) (pc + codelen c1) (by simp [codelen]; grind)
      grind [List.append_assoc, List.append_eq]

theorem compile_aexp_correct (C : List instr) (s : store) (a : aexp) (pc : Int) (stk : stack) :
  code_at C pc (compile_aexp a) →
  transitions C (pc, stk, s) (pc + codelen (compile_aexp a), aeval s a :: stk, s) := by
    induction a generalizing C pc stk
    next =>
      simp [aeval, compile_aexp]
      intro a
      unfold transitions
      apply star_one
      apply transition.trans_const
      cases a
      next => simp ; apply instr_a; grind
    next =>
      simp [aeval, compile_aexp]
      intro a
      apply star_one
      apply transition.trans_var
      cases a
      next => simp ; apply instr_a; grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      . apply a1_ih
        grind
      . apply star_trans
        . specialize a2_ih C (pc + codelen (compile_aexp a1)) (aeval s a1 :: stk)
          apply a2_ih
          grind
        . apply star_one
          cases a
          next c1 c3 a =>
            have h1 := instr_a instr.Iadd c3 (c1 ++ compile_aexp a1 ++ compile_aexp a2) (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) (by grind)
            have h2 := @transition.trans_add ((c1 ++ compile_aexp a1 ++ compile_aexp a2).append (instr.Iadd :: c3)) (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) stk s (aeval s a1) (aeval s a2) (by grind)
            simp [codelen_app, codelen_cons, codelen] at *
            grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      . apply a1_ih
        . grind
      . apply star_trans
        . specialize a2_ih C (pc + codelen (compile_aexp a1)) (aeval s a1 :: stk)
          apply a2_ih
          grind
        . apply star_trans
          . apply star_one
            . have := @transition.trans_opp C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) ((aeval s a1) ::stk) s (aeval s a2)
              apply this
              grind
          . apply star_one
            . have := @code_at_to_instr_at C pc (compile_aexp a1 ++ compile_aexp a2 ++ [instr.Iopp])  instr.Iadd [] (by grind [List.append_assoc, List.cons_append, List.nil_append])
              have := @transition.trans_add C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2) + 1) stk s (aeval s a1) (-aeval s a2) (by simp [codelen] at *; grind)
              simp [codelen] at *
              grind































-- - (* CONST *)
--   apply star_one. apply trans_const. eauto with code.

-- - (* VAR *)
--   apply star_one. apply trans_var. eauto with code.

-- - (* PLUS *)
--   eapply star_trans. apply IHa1. eauto with code.
--   eapply star_trans. apply IHa2. eauto with code.
--   apply star_one. autorewrite with code. apply trans_add. eauto with code.

-- - (* MINUS *)
--   eapply star_trans. apply IHa1. eauto with code.
--   eapply star_trans. apply IHa2. eauto with code.
--   eapply star_trans.
--   apply star_one. apply trans_opp. eauto with code.
--   apply star_one.
--   replace (aeval s a1 - aeval s a2)
--      with (aeval s a1 + (- aeval s a2))
--        by lia.
--   autorewrite with code. apply trans_add. eauto with code.
-- Qed.

-- (** The proof for the compilation of Boolean expressions is similar.
--   We recall the informal specification for the code generated by
--   [compile_bexp b d1 d0]: it should
-- - skip [d1] instructions if [b] evaluates to true,
--        [d0] if [b] evaluates to false
-- - leave the stack unchanged
-- - leave the store unchanged.
-- *)

-- Lemma compile_bexp_correct:
--   forall C s b d1 d0 pc stk,
--   code_at C pc (compile_bexp b d1 d0) ->
--   transitions C
--        (pc, stk, s)
--        (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s).
-- Proof.
--   induction b; cbn; intros.

-- - (* TRUE *)
--   destruct (d1 =? 0) eqn:Z.
--   + (* distance is zero, no branch is generated *)
--     assert (d1 = 0) by (apply Z.eqb_eq; auto). subst d1.
--     autorewrite with code. apply star_refl.
--   + (* a branch is generated *)
--     apply star_one. apply trans_branch with (d := d1). eauto with code. auto.

-- - (* FALSE *)
--   destruct (d0 =? 0) eqn:Z.
--   + (* distance is zero, no branch is generated *)
--     assert (d0 = 0) by (apply Z.eqb_eq; auto). subst d0.
--     autorewrite with code. apply star_refl.
--   + (* a branch is generated *)
--     apply star_one. apply trans_branch with (d := d0). eauto with code. auto.

-- - (* EQUAL *)
--   eapply star_trans. apply compile_aexp_correct with (a := a1). eauto with code.
--   eapply star_trans. apply compile_aexp_correct with (a := a2). eauto with code.
--   apply star_one. apply trans_beq with (d1 := d1) (d0 := d0). eauto with code.
--   autorewrite with code. auto.

-- - (* LESSEQUAL *)
--   eapply star_trans. apply compile_aexp_correct with (a := a1). eauto with code.
--   eapply star_trans. apply compile_aexp_correct with (a := a2). eauto with code.
--   apply star_one. apply trans_ble with (d1 := d1) (d0 := d0). eauto with code.
--   autorewrite with code. auto.

-- - (* NOT *)
--   replace (if negb (beval s b) then d1 else d0)
--      with (if beval s b then d0 else d1).
--   apply IHb. auto.
--   destruct (beval s b); auto.

-- - (* AND *)
--   set (code2 := compile_bexp b2 d1 d0) in *.
--   set (code1 := compile_bexp b1 0 (codelen code2 + d0)) in *.
--   eapply star_trans. apply IHb1. eauto with code.
--   fold code1. destruct (beval s b1); cbn.
--   + (* b1 evaluates to true, the code for b2 is executed *)
--     autorewrite with code. apply IHb2. eauto with code.
--   + (* b2 evaluates to true, the code for b2 is skipped *)
--     autorewrite with code. apply star_refl.
-- Qed.

-- (** ** 4.2 Correctness of generated code for commands, terminating case. *)

-- Lemma compile_com_correct_terminating:
--   forall s c s',
--   cexec s c s' ->
--   forall C pc stk,
--   code_at C pc (compile_com c) ->
--   transitions C
--       (pc, stk, s)
--       (pc + codelen (compile_com c), stk, s').
-- Proof.
--   induction 1; cbn; intros.

-- - (* SKIP *)
--   autorewrite with code. apply star_refl.

-- - (* ASSIGN *)
--   eapply star_trans. apply compile_aexp_correct with (a := a). eauto with code.
--   apply star_one. autorewrite with code. apply trans_setvar. eauto with code.

-- - (* SEQUENCE *)
--   eapply star_trans.
--   apply IHcexec1. eauto with code.
--   autorewrite with code. apply IHcexec2. eauto with code.

-- - (* IFTHENELSE *)
--   set (code1 := compile_com c1) in *.
--   set (code2 := compile_com c2) in *.
--   set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
--   eapply star_trans.
--   apply compile_bexp_correct with (b := b). eauto with code.
--   fold codeb. destruct (beval s b); autorewrite with code.
--   + (* the "then" branch is selected *)
--     eapply star_trans. apply IHcexec. eauto with code.
--     fold code1. apply star_one. apply trans_branch with (d := codelen code2). eauto with code. lia.
--   + (* then "else" branch is selected *)
--     replace (pc + codelen codeb + codelen code1 + codelen code2 + 1)
--        with (pc + codelen codeb + codelen code1 + 1 + codelen code2) by lia.
--     apply IHcexec. eauto with code.

-- - (* WHILE stop *)
--   set (code_body := compile_com c) in *.
--   set (code_branch := compile_bexp b 0 (codelen code_body + 1)) in *.
--   set (d := - (codelen code_branch + codelen code_body + 1)) in *.
--   eapply star_trans. apply compile_bexp_correct with (b := b). eauto with code.
--   rewrite H. fold code_branch. autorewrite with code. apply star_refl.

-- - (* WHILE loop *)
--   set (code_body := compile_com c) in *.
--   set (code_branch := compile_bexp b 0 (codelen code_body + 1)) in *.
--   set (d := - (codelen code_branch + codelen code_body + 1)) in *.
--   eapply star_trans. apply compile_bexp_correct with (b := b). eauto with code.
--   rewrite H. fold code_branch. autorewrite with code.
--   eapply star_trans. apply IHcexec1. eauto with code.
--   eapply star_trans.
--   apply star_one. apply trans_branch with (d := d). eauto with code. eauto.
--   replace (pc + codelen code_branch + codelen code_body + 1 + d)
--      with pc
--        by lia.
--   replace (pc + codelen code_branch + codelen code_body + 1)
--      with (pc + codelen (compile_com (WHILE b c)))
--        by (cbn; autorewrite with code; auto).
--   apply IHcexec2. auto.
-- Qed.

-- (** As a corollary, we obtain the correctness of the compilation of whole
--   programs, assuming they terminate. *)

-- Theorem compile_program_correct_terminating:
--   forall s c s',
--   cexec s c s' ->
--   machine_terminates (compile_program c) s s'.
-- Proof.
--   intros.
--   set (C := compile_program c).
--   assert (CODEAT: code_at C 0 (compile_com c ++ Ihalt :: nil)).
--   { replace C with (nil ++ compile_program c ++ nil).
--     apply code_at_intro. auto.
--     rewrite app_nil_r; auto. }
--   unfold machine_terminates.
--   exists (0 + codelen (compile_com c)); split.
-- - apply compile_com_correct_terminating. auto. eauto with code.
-- - eauto with code.
-- Qed.

-- (** *** Exercise (2 stars, recommended). *)

-- (** In a previous exercise, you modified [compile_com] to use
--   [smart_Ibranch] instead of [Ibranch] so as to generate better code.
--   Adapt the proof of [compile_com_correct_terminating] accordingly.
--   Hint: first prove the following lemma, then use it! *)

-- Lemma transitions_smart_Ibranch:
--   forall C pc d pc' stk s,
--   code_at C pc (smart_Ibranch d) ->
--   pc' = pc + 1 + d ->
--   transitions C (pc, stk, s) (pc', stk, s).
-- Proof.
--   unfold smart_Ibranch; intros.
--   (* FILL IN HERE *)
-- Abort.

-- (** *** Exercise (4 stars, optional). *)

-- (** Consider a loop with a simple test, such as [WHILE (LESSEQUAL a1 a2) c].
--   Currently, the compiled code executes two branch instructions per iteration
--   of the loop: one [Ible] to test the condition and one [Ibranch] to go back to
--   the beginning of the loop.  We can reduce this to one [Ible] instruction
--   per iteration, by putting the code for [c] before the code for the test:
-- <<
--      compile_com c ++ compile_bexp b delta1 0
-- >>
--   with [delta1] chosen so as to branch back to the beginning of [compile_com c]
--   when [b] is true.

--   By itself, this would compile while loops like do-while loops, which is
--   incorrect.  On the first iteration, we must skip over the code for [c]
--   and branch to the code that tests [b]:
-- <<
--     Ibranch (codesize(compile_com c)) :: compile_com c ++ compile_bexp b delta1 0
-- >>
--   In this exercise, you should modify [compile_com] to implement this
--   alternate compilation schema for loops, then show its correctness
--   by updating the statement and proof of [compile_com_correct_terminating].
--   The difficulty (and the reason for the 4 stars) is that the hypothesis
--   [code_at C pc (compile_com c)] no longer holds if [c] is a while loop
--   and we are at the second iteration of the loop.  You need to come up
--   with a more flexible way to relate the command [c] and the PC.
-- *)

-- (** * 7.  Full proof of compiler correctness *)

-- (** We would like to strengthen the correctness result above so that it
--   is not restricted to terminating source programs, but also applies to
--   source program that diverge.  To this end, we abandon the big-step
--   semantics for commands and switch to the small-step semantics with
--   continuations.  We then show a simulation theorem, establishing that
--   every transition of the small-step semantics in the source program
--   is simulated (in a sense to be made precise below) by zero, one or
--   several transitions of the machine executing the compiled code for
--   the source program. *)

-- (** Our first task is to relate configurations [(c, k, s)] of the small-step
--   semantics with configurations [(C, pc, stk, s)] of the machine.
--   We already know how to relate a command [c] with the machine code,
--   using the [codeseq_at] predicate.  What needs to be defined is a relation
--   between the continuation [k] and the machine code.

--   Intuitively, when the machine finishes executing the generated code for
--   command [c], that is, when it reaches the program point
--   [pc + length(compile_com c)], the machine should continue by executing
--   instructions that perform the pending computations described by
--   continuation [k], then reach an [Ihalt] instruction to stop cleanly.

--   We formalize this intution by the following inductive predicate
--   [compile_cont C k pc], which states that, starting at program point [pc],
--   there are instructions that perform the computations described in [k]
--   and reach an [Ihalt] instruction. *)

-- Inductive compile_cont (C: code): cont -> Z -> Prop :=
--   | ccont_stop: forall pc,
--       instr_at C pc = Some Ihalt ->
--       compile_cont C Kstop pc
--   | ccont_seq: forall c k pc pc',
--       code_at C pc (compile_com c) ->
--       pc' = pc + codelen (compile_com c) ->
--       compile_cont C k pc' ->
--       compile_cont C (Kseq c k) pc
--   | ccont_while: forall b c k pc d pc' pc'',
--       instr_at C pc = Some(Ibranch d) ->
--       pc' = pc + 1 + d ->
--       code_at C pc' (compile_com (WHILE b c)) ->
--       pc'' = pc' + codelen (compile_com (WHILE b c)) ->
--       compile_cont C k pc'' ->
--       compile_cont C (Kwhile b c k) pc
--   | ccont_branch: forall d k pc pc',
--       instr_at C pc = Some(Ibranch d) ->
--       pc' = pc + 1 + d ->
--       compile_cont C k pc' ->
--       compile_cont C k pc.

-- (** Then, a configuration [(c,k,s)] of the small-step semantics matches
--   a configuration [(C, pc, stk, s')] of the machine if the following conditions hold:
-- - The stores are identical: [s' = s].
-- - The machine stack is empty: [stk = nil].
-- - The machine code at point [pc] is the compiled code for [c]:
--   [code_at C pc (compile_com c)].
-- - The machine code at point [pc + codelen (compile_com c)] matches continuation
--   [k], in the sense of [compile_cont] above.
-- *)

-- Inductive match_config (C: code): com * cont * store -> config -> Prop :=
--   | match_config_intro: forall c k st pc,
--       code_at C pc (compile_com c) ->
--       compile_cont C k (pc + codelen (compile_com c)) ->
--       match_config C (c, k, st) (pc, nil, st).

-- (** We are now ready to prove the expected simulation property.
--   Since some transitions in the source command correspond to zero transitions
--   in the compiled code, we need a simulation diagram of the "star" kind
--   (see the slides).
-- <<
--                       match_config
--      c / k / st  ----------------------- machconfig
--        |                                   |
--        |                                   | + or ( * and |c',k'| < |c,k} )
--        |                                   |
--        v                                   v
--     c' / k' / st' ----------------------- machconfig'
--                       match_config
-- >>
-- Note the stronger conclusion on the right:
-- - either the virtual machine does one or several transitions
-- - or it does zero, one or several transitions, but the size of the [c,k]
--   pair decreases strictly.

-- It would be equivalent to state:
-- - either the virtual machine does one or several transitions
-- - or it does zero transitions, but the size of the [c,k] pair decreases strictly.

-- However, the formulation above, with the "star" case, is often more convenient.
-- *)

-- (** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
--   After trial and error, we find that the following measure works.  It is
--   the sum of the sizes of the command [c] under focus and all the commands
--   appearing in the continuation [k]. *)

-- Fixpoint com_size (c: com) : nat :=
--   match c with
--   | SKIP => 1%nat
--   | ASSIGN x a => 1%nat
--   | (c1 ;; c2) => (com_size c1 + com_size c2 + 1)%nat
--   | IFTHENELSE b c1 c2 => (com_size c1 + com_size c2 + 1)%nat
--   | WHILE b c1 => (com_size c1 + 1)%nat
--   end.

-- Remark com_size_nonzero: forall c, (com_size c > 0)%nat.
-- Proof.
--   induction c; cbn; lia.
-- Qed.

-- Fixpoint cont_size (k: cont) : nat :=
--   match k with
--   | Kstop => 0%nat
--   | Kseq c k' => (com_size c + cont_size k')%nat
--   | Kwhile b c k' => cont_size k'
--   end.

-- Definition measure (impconf: com * cont * store) : nat :=
--   match impconf with (c, k, m) => (com_size c + cont_size k)%nat end.

-- (** A few technical lemmas to help with the simulation proof. *)

-- Lemma compile_cont_Kstop_inv:
--   forall C pc s,
--   compile_cont C Kstop pc ->
--   exists pc',
--   star (transition C) (pc, nil, s) (pc', nil, s)
--   /\ instr_at C pc' = Some Ihalt.
-- Proof.
--   intros. dependent induction H.
-- - exists pc; split. apply star_refl. auto.
-- - destruct IHcompile_cont as (pc'' & A & B); auto.
--   exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch; eauto.
-- Qed.

-- Lemma compile_cont_Kseq_inv:
--   forall C c k pc s,
--   compile_cont C (Kseq c k) pc ->
--   exists pc',
--   star (transition C) (pc, nil, s) (pc', nil, s)
--   /\ code_at C pc' (compile_com c)
--   /\ compile_cont C k (pc' + codelen(compile_com c)).
-- Proof.
--   intros. dependent induction H.
-- - exists pc; split. apply star_refl. split; congruence.
-- - edestruct IHcompile_cont as (pc'' & A & B). eauto.
--   exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch; eauto.
-- Qed.

-- Lemma compile_cont_Kwhile_inv:
--   forall C b c k pc s,
--   compile_cont C (Kwhile b c k) pc ->
--   exists pc',
--   plus (transition C) (pc, nil, s) (pc', nil, s)
--   /\ code_at C pc' (compile_com (WHILE b c))
--   /\ compile_cont C k (pc' + codelen(compile_com (WHILE b c))).
-- Proof.
--   intros. dependent induction H.
-- - exists (pc + 1 + d); split.
--   apply plus_one. eapply trans_branch; eauto.
--   split; congruence.
-- - edestruct IHcompile_cont as (pc'' & A & B & D). eauto.
--   exists pc''; split; auto. eapply plus_left. eapply trans_branch; eauto. apply plus_star; auto.
-- Qed.

-- Lemma match_config_skip:
--   forall C k s pc,
--   compile_cont C k pc ->
--   match_config C (SKIP, k, s) (pc, nil, s).
-- Proof.
--   intros. constructor.
-- - cbn. inversion H; eauto with code.
-- - cbn. autorewrite with code. auto.
-- Qed.

-- (** At last, we can state and prove the simulation diagram. *)

-- Lemma simulation_step:
--   forall C impconf1 impconf2 machconf1,
--   step impconf1 impconf2 ->
--   match_config C impconf1 machconf1 ->
--   exists machconf2,
--       (plus (transition C) machconf1 machconf2
--        \/ (star (transition C) machconf1 machconf2
--            /\ (measure impconf2 < measure impconf1)%nat))
--    /\ match_config C impconf2 machconf2.
-- Proof.
--   intros until machconf1; intros STEP MATCH.
--   inversion STEP; clear STEP; subst; inversion MATCH; clear MATCH; subst; cbn in *.

-- - (* assign *)
--   econstructor; split.
--   left. eapply plus_right. eapply compile_aexp_correct; eauto with code.
--   eapply trans_setvar; eauto with code.
--   autorewrite with code in *. apply match_config_skip. auto.

-- - (* seq *)
--   econstructor; split.
--   right; split. apply star_refl. lia.
--   autorewrite with code in *. constructor. eauto with code. eapply ccont_seq; eauto with code.

-- - (* if *)
--   set (code1 := compile_com c1) in *.
--   set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
--   set (code2 := compile_com c2) in *.
--   autorewrite with code in *.
--   econstructor; split.
--   right; split.
--   apply compile_bexp_correct with (b := b). eauto with code.
--   destruct (beval s b); lia.
--   fold codeb. destruct (beval s b).
--   + autorewrite with code. constructor. eauto with code.
--     eapply ccont_branch. eauto with code. eauto.
--     fold code1.
--     replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
--        with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
--     auto.
--   + autorewrite with code. constructor. eauto with code. auto.
--     fold code2.
--     replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
--        with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
--     auto.

-- - (* while stop *)
--   set (codec := compile_com c) in *.
--   set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
--   econstructor; split.
--   right; split.
--   apply compile_bexp_correct with (b := b). eauto with code.
--   assert (com_size c > 0)%nat by apply com_size_nonzero. lia.
--   rewrite H. fold codeb. autorewrite with code in *. apply match_config_skip. auto.

-- - (* while loop *)
--   set (codec := compile_com c) in *.
--   set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
--   econstructor; split.
--   right; split.
--   apply compile_bexp_correct with (b := b). eauto with code.
--   lia.
--   rewrite H. fold codeb. autorewrite with code in *.
--   constructor. eauto with code.
--   eapply ccont_while with (pc' := pc). eauto with code. fold codec. lia.
--   auto.
--   cbn. fold codec; fold codeb. eauto.
--   autorewrite with code. auto.

-- - (* skip seq *)
--   autorewrite with code in *.
--   edestruct compile_cont_Kseq_inv as (pc' & X & Y & Z). eauto.
--   econstructor; split.
--   right; split. eauto. lia.
--   constructor; auto.

-- - (* skip while *)
--   autorewrite with code in *.
--   edestruct compile_cont_Kwhile_inv as (pc' & X & Y & Z). eauto.
--   econstructor; split.
--   left. eauto.
--   constructor; auto.
-- Qed.

-- (** The hard work is done!  Nice consequences will follow. *)

-- (** First, we get an alternate proof of [compile_program_correct_terminating],
--   using the continuation semantics instead of the big-step semantics
--   to characterize termination of the source program. *)

-- Lemma simulation_steps:
--   forall C impconf1 impconf2, star step impconf1 impconf2 ->
--   forall machconf1, match_config C impconf1 machconf1 ->
--   exists machconf2,
--      star (transition C) machconf1 machconf2
--   /\ match_config C impconf2 machconf2.
-- Proof.
--   induction 1; intros.
-- - exists machconf1; split; auto. apply star_refl.
-- - edestruct simulation_step as (machconf2 & STEPS2 & MATCH2); eauto.
--   edestruct IHstar as (machconf3 & STEPS3 & MATCH3); eauto.
--   exists machconf3; split; auto.
--   eapply star_trans; eauto.
--   destruct STEPS2 as [A | [A B]]. apply plus_star; auto. auto.
-- Qed.

-- Lemma match_initial_configs:
--   forall c s,
--   match_config (compile_program c) (c, Kstop, s) (0, nil, s).
-- Proof.
--   intros. set (C := compile_program c).
--   assert (code_at C 0 (compile_com c ++ Ihalt :: nil)).
--   { replace C with (nil ++ (compile_com c ++ Ihalt :: nil) ++ nil).
--     constructor; auto.
--     rewrite app_nil_r; auto. }
--   constructor.
-- - eauto with code.
-- - apply ccont_stop. eauto with code.
-- Qed.

-- Theorem compile_program_correct_terminating_2:
--   forall c s s',
--   star step (c, Kstop, s) (SKIP, Kstop, s') ->
--   machine_terminates (compile_program c) s s'.
-- Proof.
--   intros. set (C := compile_program c).
--   edestruct (simulation_steps C) as (ms & A & B). eauto. apply match_initial_configs.
--   inversion B; subst.
--   edestruct compile_cont_Kstop_inv as (pc' & D & E). eauto.
--   exists pc'; split; auto.
--   eapply star_trans. eauto. cbn in D; autorewrite with code in D. eauto.
-- Qed.

-- (** Second, and more importantly, we get a proof of semantic preservation
--   for diverging source programs: if the program makes infinitely many steps,
--   the generated code makes infinitely many machine transitions. *)

-- Lemma simulation_infseq_inv:
--   forall C n impconf1 machconf1,
--   infseq step impconf1 -> match_config C impconf1 machconf1 ->
--   (measure impconf1 < n)%nat ->
--   exists impconf2 machconf2,
--       infseq step impconf2
--    /\ plus (transition C) machconf1 machconf2
--    /\ match_config C impconf2 machconf2.
-- Proof.
--   induction n; intros impconf1 machconf1 INFSEQ MATCH MEASURE.
-- - exfalso; lia.
-- - inversion INFSEQ; clear INFSEQ; subst.
--   edestruct simulation_step as (machconf2 & [PLUS | [STAR LESS]] & MATCH2). eauto. eauto.
-- + exists b, machconf2; auto.
-- + edestruct IHn as (impconf3 & machconf3 & X & Y & Z). eauto. eauto. lia.
--   exists impconf3, machconf3.
--   split. auto.
--   split. eapply star_plus_trans; eauto.
--   auto.
-- Qed.

-- Theorem compile_program_correct_diverging:
--   forall c s,
--   infseq step (c, Kstop, s) ->
--   machine_diverges (compile_program c) s.
-- Proof.
--   intros. set (C := compile_program c).
--   apply infseq_coinduction_principle_2 with
--     (X := fun machconf =>
--           exists impconf, infseq step impconf /\ match_config C impconf machconf).
-- - intros machconf (impconf & INFSEQ & MATCH).
--   edestruct (simulation_infseq_inv C (S (measure impconf)))
--   as (impconf2 & machconf2 & INFSEQ2 & PLUS & MATCH2).
--   eauto. eauto. lia.
--   exists machconf2; split. auto. exists impconf2; auto.
-- - exists (c, Kstop, s); split. auto. apply match_initial_configs.
-- Qed.
