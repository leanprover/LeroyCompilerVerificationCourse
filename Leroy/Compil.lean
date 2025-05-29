import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic

set_option grind.warning false
set_option grind.debug true
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

@[grind] def transitions (C: List instr) : config → config → Prop :=
  star (transition C)

def machine_terminates (C: List instr) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

def machine_goes_wrong (C: List instr) (s_init: store) : Prop :=
  exists pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

@[grind] def compile_aexp (a: aexp) : List instr :=
  match a with
  | .CONST n => .Iconst n :: []
  | .VAR x => .Ivar x :: []
  | .PLUS a1 a2  => (compile_aexp a1) ++ (compile_aexp a2) ++ (.Iadd :: [])
  | .MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ (.Iopp :: .Iadd :: [])

@[grind] def compile_bexp (b: bexp) (d1: Int) (d0: Int) : List instr :=
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

@[grind] def compile_com (c: com) : List instr:=
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

@[grind] theorem codelen_singleton : codelen [i] = 1 := by
  dsimp [codelen]

@[grind] theorem codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 _
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
            . have := @transition.trans_opp C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) ((aeval s a1) :: stk) s (aeval s a2)
              apply this
              grind
          . apply star_one
            . have := @code_at_to_instr_at C pc (compile_aexp a1 ++ compile_aexp a2 ++ [instr.Iopp])  instr.Iadd [] (by grind [List.append_assoc, List.cons_append, List.nil_append])
              have := @transition.trans_add C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2) + 1) stk s (aeval s a1) (-aeval s a2) (by simp [codelen] at *; grind)
              simp [codelen] at *
              grind
-- Miss 5
theorem compile_bexp_correct (C : List instr) (s : store) (b : bexp) (d1 d0 : Int) (pc : Int) (stk : stack) (h : code_at C pc (compile_bexp b d1 d0))  :
   transitions C
       (pc, stk, s)
       (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s) := by
    induction b generalizing d1 d0 pc
    next =>
      simp [compile_bexp, beval]
      by_cases d1 = 0
      case pos is_zero =>
        simp [is_zero, codelen]
        apply star.star_refl
      case neg is_not_zero =>
        apply star_one
        simp [is_not_zero, codelen]
        apply transition.trans_branch _ _ _ d1
        . simp [compile_bexp, is_not_zero] at h
          have := @code_at_to_instr_at C pc [] (instr.Ibranch d1) [] (by grind [List.append_assoc, List.nil_append])
          grind
        . grind
    next =>
      simp [compile_bexp, beval]
      by_cases d0 = 0
      case pos is_zero =>
        simp [is_zero, codelen]
        apply star.star_refl
      case neg is_not_zero =>
        apply star_one
        simp [is_not_zero, codelen]
        apply transition.trans_branch _ _ _ d0
        . simp [compile_bexp, is_not_zero] at h
          have := @code_at_to_instr_at C pc [] (instr.Ibranch d0) [] (by grind [List.append_assoc, List.nil_append])
          grind
        . grind
    next a1 a2 =>
      simp [compile_bexp, beval]
      apply star_trans
      . apply compile_aexp_correct
        rotate_left
        . exact a1
        . simp [compile_bexp] at h
          grind
      . apply star_trans
        . apply compile_aexp_correct
          rotate_right
          . exact a2
          . simp [compile_bexp] at h
            grind
        . apply star_one
          . apply transition.trans_beq
            rotate_left; rotate_left
            . exact d1
            . exact d0
            . simp [compile_bexp] at h
              grind
            . grind
    next a1 a2 =>
      simp [compile_bexp, beval]
      apply star_trans
      . apply compile_aexp_correct
        rotate_left
        . exact a1
        . simp [compile_bexp] at h
          grind
      . apply star_trans
        . apply compile_aexp_correct
          rotate_right
          . exact a2
          . simp [compile_bexp] at h
            grind
        . apply star_one
          . apply transition.trans_ble
            rotate_left; rotate_left
            . exact d1
            . exact d0
            . simp [compile_bexp] at h
              grind
            . grind
    next b1 ih =>
      simp [compile_bexp, beval] at *
      have := ih d0 d1 pc
      grind
    next b1 b2 b1_ih b2_ih =>
      generalize heq1 : compile_bexp b2 d1 d0 = code2
      generalize heq2 : compile_bexp b1 0 (codelen code2 + d0) = code1
      unfold compile_bexp
      simp [heq1, heq2]
      apply star_trans
      . apply b1_ih
        rotate_left
        . exact 0
        . exact (codelen code2 + d0)
        . rw [heq2]
          unfold compile_bexp at h
          simp [heq1, heq2] at h
          apply code_at_app_left
          exact h
      . by_cases beval s b1 = true
        case pos isTrue =>
          simp [isTrue]
          rw [heq2]
          simp [beval, isTrue]
          specialize b2_ih d1 d0 (pc + codelen code1)
          rw [heq1] at b2_ih
          simp [compile_bexp, heq1, heq2] at h
          specialize b2_ih (by grind)
          simp [codelen_app]
          -- Why is grind not working here?
          simp [Int.add_assoc] at *
          exact b2_ih
        case neg isFalse =>
          simp [beval, isFalse]
          rw [heq2]
          simp [codelen_app]
          grind

theorem compile_com_correct_terminating (s s' : store) (c : com) (h₁ : cexec s c s') :
 ∀ C pc stk, code_at C pc (compile_com c) →
  transitions C
      (pc, stk, s)
      (pc + codelen (compile_com c), stk, s') := by
  induction h₁
  case cexec_skip =>
    intro C pc stk h
    unfold compile_com
    dsimp [codelen]
    simp only [Int.add_zero]
    apply star.star_refl
  case cexec_assign s' x a =>
    intro C pc stk h
    unfold compile_com
    apply star_trans
    . apply compile_aexp_correct
      rotate_left
      . exact a
      . unfold compile_com at h
        grind
    . apply star_one
      . have := @transition.trans_setvar C (pc + codelen (compile_aexp a)) stk s x (aeval s a)
        rw [codelen_app, codelen_singleton]
        suffices transition C (pc + codelen (compile_aexp a), aeval s a :: stk, s) (pc + codelen (compile_aexp a) + 1, stk, update x (aeval s a) s) from by grind
        apply this
        grind
  case cexec_seq s'2 c1 s1 c2 s2 cexec1 cexec2 c1_ih c2_ih =>
    intro C pc stk h
    apply star_trans
    . apply c1_ih
      unfold compile_com at h
      apply code_at_app_left
      exact h
    . specialize c2_ih C (pc + codelen (compile_com c1)) stk
      simp [compile_com, codelen_app, Int.add_assoc]
      simp [Int.add_assoc] at c2_ih
      apply c2_ih
      grind
  case cexec_ifthenelse s b c1 c2 s' cexec_h ih =>
    intro C pc stk
    generalize heq1 : compile_com c1 = code1
    generalize heq2 : compile_com c2 = code2
    generalize heq3 : compile_bexp b 0 (codelen code1 + 1) = code3
    simp [compile_com]
    rw [heq1, heq2, heq3]
    intro h
    apply star_trans
    . have := compile_bexp_correct C s b 0 (codelen code1 + 1) pc stk (by grind)
      apply this
    . by_cases beval s b = true
      case pos isTrue =>
        -- The "then" branch is selected
        simp [isTrue]
        apply star_trans
        . apply ih
          simp [isTrue, heq1, heq3]
          grind
        . apply star_one
          . apply transition.trans_branch
            rotate_right
            . exact codelen code2
            . simp [isTrue]
              rw [heq3, heq1]
              have := @code_at_to_instr_at C pc (code3 ++ code1) (instr.Ibranch (codelen code2)) code2 (by grind)
              simp [codelen] at *
              grind
            . rw [heq3]
              grind
      case neg isFalse =>
        simp [isFalse]
        rw [heq3]
        specialize ih C (pc + codelen code3 + (codelen code1 + 1)) stk
        simp [isFalse] at ih
        suffices h2 : code_at C (pc + codelen code3 + (codelen code1 + 1)) (compile_com c2) from by
          specialize ih h2
          simp [codelen_app, codelen_cons]
          -- grind is failing here - same issue as miss 2
          have : (pc + codelen code3 + (codelen code1 + 1) + codelen (compile_com c2)) = (pc + (codelen code3 + (codelen code1 + (codelen code2 + 1)))) := by grind
          rw [this] at ih
          apply ih
        -- In the last argument grind fails
        have := @code_at_app_right C pc (code3 ++ code1 ++ [instr.Ibranch (codelen code2)]) code2 (by simp[h])
        simp [codelen_app, codelen_singleton] at this
        rw [heq2]
        grind
  case cexec_while_done s b c1 isFalse =>
    intro C pc stk h
    generalize heq1 : compile_com c1 = code_body
    generalize heq2 : compile_bexp b 0 (codelen code_body + 1) = code_branch
    generalize heq3 : - (codelen code_branch + codelen code_body + 1) = d
    simp [compile_com]
    rw [heq1, heq2, heq3]
    simp [codelen_app, codelen_singleton]
    apply star_trans
    .  apply compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk (by grind)
    . simp [isFalse]
      grind
  case cexec_while_loop s b c1 s_intermediate s' isTrue cexec1 cexec2 ih1 ih2 =>
    intro C pc stk
    generalize heq1 : compile_com c1 = code_body
    generalize heq2 : compile_bexp b 0 (codelen code_body + 1) = code_branch
    generalize heq3 : - (codelen code_branch + codelen code_body + 1) = d
    simp [compile_com]
    rw [heq1, heq2, heq3]
    intro h
    apply star_trans
    . apply compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk (by grind)
    . apply star_trans
      . simp [isTrue]
        rw [heq2]
        specialize ih1 C (pc + codelen code_branch) stk
        apply ih1
        grind
      . apply star_trans
        . apply star_one
          apply transition.trans_branch
          rotate_left
          rotate_left
          . exact d
          . exact (pc + codelen code_branch + codelen code_body + 1 + d)
          . apply @code_at_to_instr_at
            rotate_left
            . exact []
            . apply code_at_app_right
              grind [List.append_assoc]
          . grind
        . specialize ih2 C (pc + codelen code_branch + codelen code_body + 1 + d) stk
          suffices h2 : code_at C (pc + codelen code_branch + codelen code_body + 1 + d) (compile_com (com.WHILE b c1)) from by
            specialize ih2 h2
            simp [compile_com] at ih2
            rw [heq1, heq2, heq3] at ih2
            simp [codelen_app]
            simp [codelen_app] at ih2
            -- grind is not managing to solve the arithmetic goal here
            have : (pc + codelen code_branch + codelen code_body + 1 + d +
      (codelen code_branch + (codelen code_body + codelen [instr.Ibranch d])) ) = (pc + (codelen code_branch + (codelen code_body + codelen [instr.Ibranch d]))) := by grind
            rw [←this]
            apply ih2
          rw [←heq3]
          suffices h3 : (pc + codelen code_branch + codelen code_body + 1 + -(codelen code_branch + codelen code_body + 1)) = pc from by
            rw [h3]
            simp [compile_com]
            rw [heq1, heq2, heq3]
            exact h
          grind

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

inductive compile_cont (C: List instr) : cont -> Int -> Prop where
  | ccont_stop: forall pc,
      instr_at C pc = .some .Ihalt ->
      compile_cont C .Kstop pc
  | ccont_seq: forall c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (.Kseq c k) pc
  | ccont_while: forall b c k pc d pc' pc'',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (.WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (.WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (.Kwhile b c k) pc
  | ccont_branch: forall d k pc pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc

-- (** Then, a configuration [(c,k,s)] of the small-step semantics matches
--   a configuration [(C, pc, stk, s')] of the machine if the following conditions hold:
-- - The stores are identical: [s' = s].
-- - The machine stack is empty: [stk = nil].
-- - The machine code at point [pc] is the compiled code for [c]:
--   [code_at C pc (compile_com c)].
-- - The machine code at point [pc + codelen (compile_com c)] matches continuation
--   [k], in the sense of [compile_cont] above.
-- *)
inductive match_config (C: List instr): com × cont × store -> config -> Prop where
  | match_config_intro: forall c k st pc,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st) (pc, [], st)

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

def com_size (c: com) : Nat :=
  match c with
  | .SKIP => 1
  |.ASSIGN _ _ => 1
  | (c1 ;; c2) => (com_size c1 + com_size c2 + 1)
  | .IFTHENELSE _ c1 c2 => (com_size c1 + com_size c2 + 1)
  | .WHILE _ c1 => (com_size c1 + 1)


theorem com_size_nonzero: forall c, (com_size c > 0) := by
  intro c
  fun_induction com_size <;> grind

def cont_size (k: cont) : Nat :=
  match k with
  | .Kstop => 0
  | .Kseq c k' => (com_size c + cont_size k')
  | .Kwhile _ _ k' => cont_size k'

def measure' (impconf: com × cont × store) : Nat :=
  match impconf with
  | (c, k, _) => (com_size c + cont_size k)

theorem compile_cont_Kstop_inv (C : List instr) (pc : Int) (s : store):
  compile_cont C .Kstop pc →
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ instr_at C pc' = .some .Ihalt := by
    intro H
    generalize h₁ : cont.Kstop = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc <;> grind

theorem compile_cont_Kseq_inv (C : List instr) (c : com) (k :cont) (pc : Int) (s : store) (H : compile_cont C (.Kseq c k) pc):
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com c)
  ∧ compile_cont C k (pc' + codelen (compile_com c)) := by
    generalize h₁ : (cont.Kseq c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k
    any_goals grind
    case ccont_seq c' k' pc₂ pc₃ a₃ a₄ a₅ ih =>
      exists pc₂
      injection h₁
      rename_i h₃ h₄
      apply And.intro
      . apply star.star_refl
      . all_goals grind

theorem compile_cont_Kwhile_inv (C : List instr) (b : bexp) (c : com) (k : cont) (pc : Int) (s : store) (H : compile_cont C (.Kwhile b c k) pc):
  ∃ pc',
  plus (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com (.WHILE b c))
  ∧ compile_cont C k (pc' + codelen (compile_com (.WHILE b c))) := by
    generalize h₁ : (cont.Kwhile b c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k
    any_goals grind
    case ccont_branch d k' pc₂ pc₃ h₃ h₄ h₅ ih =>
      specialize ih k pc₃ h₁ rfl
      apply Exists.elim ih
      intro pc₄ ih
      exists pc₄
      apply And.intro
      . rw [h₄] at ih
        rw [←h₂]
        rw [←h₂] at ih
        apply plus.plus_left
        rotate_left
        . apply plus_star
          exact ih.1
        . apply transition.trans_branch
          rotate_left
          . exact rfl
          . rw [←h₂] at h₃
            exact h₃
      . grind
    case ccont_while b' c' k' pc₂ d pc₃ pc₄ h₃ h₄ h₅ h₆ h₇ ih =>
      exists (pc + 1 + d)
      constructor
      apply plus_one
      apply transition.trans_branch
      rotate_left 2
      . exact d
      any_goals grind

theorem match_config_skip (C : List instr) (k : cont) (s : store) (pc : Int) (H: compile_cont C k pc):
 match_config C (.SKIP, k, s) (pc, [], s) := by
  constructor
  . simp [compile_com]
    cases H <;> grind
  . simp [compile_com, codelen]
    exact H

theorem simulation_step:
  forall C impconf1 impconf2 machconf1,
  step impconf1 impconf2 ->
  match_config C impconf1 machconf1 ->
  exists machconf2,
      (plus (transition C) machconf1 machconf2
       \/ (star (transition C) machconf1 machconf2
           /\ (measure' impconf2 < measure' impconf1)))
   /\ match_config C impconf2 machconf2 := by
    intro C impconf1 impconf2 matchconf1 STEP MATCH
    cases MATCH
    case match_config_intro c k st pc h₁ h₂ =>
      rcases impconf2 with ⟨c' , k', s'⟩
      cases STEP
      next x a =>
        constructor
        constructor
        case h.left =>
          apply Or.intro_left
          apply plus_right
          apply compile_aexp_correct
          rotate_left
          exact a
          rotate_left
          . simp [compile_com] at h₁
            grind
          . apply transition.trans_setvar
            simp [compile_com] at h₁
            rotate_left
            exact x
            grind
        apply match_config_skip
        simp [compile_com] at h₂
        grind
      next c2 =>
        constructor
        constructor
        apply Or.intro_right
        constructor
        apply star.star_refl
        simp [measure', com_size, cont_size]
        grind
        constructor
        simp [compile_com] at h₁
        grind
        apply compile_cont.ccont_seq
        . grind
        rotate_right
        . exact pc + codelen (compile_com c') + codelen (compile_com c2)
        . rfl
        . grind
      next b c1 c2 =>
        generalize h₃ : compile_com c1 = code1
        generalize h₄ : compile_bexp b 0 (codelen code1 + 1) = codeb
        generalize h₅ : compile_com c2 = code2
        simp [compile_com, h₃, h₄, h₅] at h₁ h₂
        constructor
        constructor
        apply Or.intro_right
        constructor
        . apply compile_bexp_correct
          rotate_left
          . exact b
          . exact 0
          . exact (codelen code1 + 1)
          . rw [h₄]
            grind
        . simp [measure', com_size]
          grind
        . rw [h₄]
          constructor
          . by_cases beval st b = true
            case pos isTrue =>
              simp [isTrue] at *
              grind
            case neg isFalse =>
              simp [isFalse] at *
              rw [h₅]
              have := @code_at_app_right C pc (codeb ++ code1 ++ [instr.Ibranch (codelen code2)]) code2 (by grind [List.append_assoc, List.cons_append, List.nil_append])
              simp [codelen_cons, codelen_singleton, codelen_app] at this
              simp [codelen] at *
              grind
          . by_cases beval st b = true
            case pos isTrue =>
              simp [isTrue] at *
              apply compile_cont.ccont_branch
              rotate_right
              . exact (pc + codelen (codeb ++ (code1 ++ instr.Ibranch (codelen code2) :: code2)))
              rotate_right
              . exact codelen code2
              any_goals grind
            case neg isFalse =>
              simp [isFalse] at *
              grind
      next b c isFalse =>
        generalize h₃ : compile_com c = codec
        generalize h₄ : (compile_bexp b 0 (codelen codec + 1)) = codeb
        constructor
        constructor
        apply Or.intro_right
        constructor
        . apply compile_bexp_correct
          rotate_left
          . exact b
          . exact 0
          . exact (codelen codec + 1)
          . simp [compile_com] at h₁
            grind
        . simp [measure', com_size]
          fun_induction com_size <;> grind
        . simp [isFalse]
          rw [h₄]
          simp [compile_com] at h₂ h₁
          rw [h₃, h₄] at h₂ h₁
          constructor
          . simp [compile_com]
            grind
          . simp [codelen_app] at h₂
            grind
      next b isTrue =>
        generalize h₃ : compile_com c' = codec
        generalize h₄ : compile_bexp b 0 (codelen codec + 1) = codeb
        constructor
        constructor
        . apply Or.intro_right
          constructor
          . apply compile_bexp_correct
            rotate_left
            . exact b
            . exact 0
            . exact (codelen codec + 1)
            . simp [compile_com] at h₁
              grind
          . simp [measure', cont_size, com_size]
        . simp [isTrue]
          rw [h₄]
          constructor
          . simp [compile_com] at h₁
            rw [h₃, h₄] at h₁
            grind
          . simp [compile_com, h₃, h₄] at h₁ h₂
            apply compile_cont.ccont_while
            rotate_left 4
            . exact h₂
            . exact (-(codelen codeb + codelen codec + 1))
            rotate_left 3
            . simp [compile_com, h₃, h₄]
              exact h₁
            . grind
            . grind
            . grind
      next =>
        have := compile_cont_Kseq_inv C c' k' pc st (by simp [compile_com, codelen] at h₂; grind)
        apply Exists.elim this
        intro pc'
        intro ⟨w₁, w₂⟩
        exists (pc', [], st)
        constructor
        . apply Or.intro_right
          constructor
          . exact w₁
          . simp [measure', cont_size, com_size]
        . constructor
          . exact w₂.1
          . simp [compile_com, codelen] at h₂
            grind
      next b c =>
        have := compile_cont_Kwhile_inv C b c k' pc st (by simp [compile_com, codelen] at h₂; grind)
        apply Exists.elim this
        intro pc'
        intro ⟨ w₁, w₂ ⟩
        exists (pc', [], st)
        constructor
        . apply Or.intro_left
          . exact w₁
        . constructor
          . exact w₂.1
          . exact w₂.2


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
