import «Leroy».Sequences
import «Leroy».Imp
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

def code := List instr

instance : HAppend code code code where
  hAppend := List.append

@[grind] def codelen (c: code) : Int := c.length

def stack : Type := List Int

def config : Type := Int × stack × store

@[grind] def instr_at (C : code) (pc : Int) : Option instr :=
  match C with
  | [] => .none
  | i :: C' => if pc = 0 then .some i else instr_at C' (pc - 1)

@[grind] inductive transition (C: code): config → config → Prop where
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

def transitions (C: code) : config -> config -> Prop :=
  star (transition C)

def machine_terminates (C: code) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

def machine_goes_wrong (C: code) (s_init: store) : Prop :=
  exists pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

def compile_aexp (a: aexp) : List instr :=
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

def compile_com (c: com) : List instr :=
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

def compile_program (p: com) : code :=
  compile_com p ++ .Ihalt :: []

#eval (compile_program (.ASSIGN "x" (.PLUS (.VAR "x") (.CONST 1))))

def smart_Ibranch (d: Int) : code :=
  if d = 0 then [] else .Ibranch d :: []

@[grind] inductive code_at: code -> Int -> code -> Prop where
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2

theorem codelen_cons:
  forall i c, codelen (i :: c) = codelen c + 1 := by grind

theorem codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 c2
    induction c1
    case nil =>
      rw [List.nil_append]
      unfold codelen
      grind

theorem instr_a : forall i c2 c1 pc,
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
    case code_at_intro c1 c2 c3 pc' a =>
      rw [←heq1, ←List.append_eq]
      sorry





-- Lemma code_at_tail:
--   forall C pc i C',
--   code_at C pc (i :: C') ->
--   code_at C (pc + 1) C'.
-- Proof.
--   intros. inversion H.
--   change (C1 ++ (i :: C') ++ C3)
--     with (C1 ++ (i :: nil) ++ C' ++ C3).
--   rewrite <- app_ass. constructor. rewrite codelen_app. subst pc. auto.
-- Qed.

theorem code_at_app_left:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1 := by
    intro c pc c1 c2 H
    generalize heq : (c1 ++ c2) = x
    rw [heq] at H
    induction H
    sorry

-- Proof.
--   intros. inversion H. rewrite app_ass. constructor. auto.
-- Qed.

-- Lemma code_at_app_right:
--   forall C pc C1 C2,
--   code_at C pc (C1 ++ C2) ->
--   code_at C (pc + codelen C1) C2.
-- Proof.
--   intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite codelen_app. subst pc. auto.
-- Qed.

-- Lemma code_at_app_right2:
--   forall C pc C1 C2 C3,
--   code_at C pc (C1 ++ C2 ++ C3) ->
--   code_at C (pc + codelen C1) C2.
-- Proof.
--   intros. apply code_at_app_right. apply code_at_app_left with (C2 := C3). rewrite app_ass; auto.
-- Qed.

-- Lemma code_at_nil:
--   forall C pc C1,
--   code_at C pc C1 -> code_at C pc nil.
-- Proof.
--   intros. inversion H. subst. change (C1 ++ C3) with (nil ++ C1 ++ C3).
--   constructor. auto.
-- Qed.

-- Lemma instr_at_code_at_nil:
--   forall C pc i, instr_at C pc = Some i -> code_at C pc nil.
-- Proof.
--   induction C; cbn; intros.
-- - discriminate.
-- - destruct (pc =? 0) eqn:PC.
-- + assert (pc = 0) by (apply Z.eqb_eq; auto). subst pc.
--   change (a :: C) with (nil ++ nil ++ (a :: C)). constructor. auto.
-- + assert (A: code_at C (pc - 1) nil) by eauto.
--   inversion A; subst.
--   apply code_at_intro with (C1 := a :: C1) (C3 := C3). rewrite codelen_cons. lia.
-- Qed.
