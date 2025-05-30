import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic

set_option grind.debug true
set_option grind.warning false

@[grind] def mk_PLUS_CONST (a: aexp) (n: Int) : aexp :=
  if n = 0 then a else
  match a with
  | .CONST m => .CONST (m + n)
  | .PLUS a (.CONST m) => .PLUS a (.CONST (m + n))
  | _ => .PLUS a (.CONST n)

@[grind] def mk_PLUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | .CONST m, _ => mk_PLUS_CONST a2 m
  | _, .CONST m => mk_PLUS_CONST a1 m
  | .PLUS a1 (.CONST m1), .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.PLUS a1 a2) (m1 + m2)
  | .PLUS a1 (.CONST m1), _ => mk_PLUS_CONST (.PLUS a1 a2) m1
  | _, .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.PLUS a1 a2) m2
  | _, _ => .PLUS a1 a2

@[grind] def mk_MINUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | _, .CONST m => mk_PLUS_CONST a1 (-m)
  | .PLUS a1 (.CONST m1), .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.MINUS a1 a2) (m1 - m2)
  | .PLUS a1 (.CONST m1), _ => mk_PLUS_CONST (.MINUS a1 a2) m1
  | _, .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.MINUS a1 a2) (-m2)
  | _, _ => .MINUS a1 a2

@[grind] def simplif_aexp (a: aexp) : aexp :=
  match a with
  | .CONST n => .CONST n
  | .VAR x => .VAR x
  | .PLUS a1 a2 => mk_PLUS (simplif_aexp a1) (simplif_aexp a2)
  | .MINUS a1 a2 => mk_MINUS (simplif_aexp a1) (simplif_aexp a2)

#eval simplif_aexp (.MINUS (.PLUS (.VAR "x") (.CONST 1)) (.PLUS (.VAR "y") (.CONST 1)))

@[grind] theorem mk_PLUS_CONST_sound:
  forall s a n, aeval s (mk_PLUS_CONST a n) = aeval s a + n := by
    intro s a n
    fun_cases mk_PLUS_CONST <;> grind

theorem mk_PLUS_sound:
  forall s a1 a2, aeval s (mk_PLUS a1 a2) = aeval s a1 + aeval s a2 := by
    intro s a1 a2
    fun_cases mk_PLUS
    <;> (try (simp [aeval]) ; try (simp [mk_PLUS_CONST_sound ]) ; grind)
    next m _ =>
      grind

theorem mk_MINUS_sound:
  forall s a1 a2, aeval s (mk_MINUS a1 a2) = aeval s a1 - aeval s a2 := by
    intro s a1 a2
    fun_cases mk_MINUS a1 a2 <;> (try (simp [aeval]) ; try (simp [mk_PLUS_CONST_sound ]) ; grind)

theorem simplif_aexp_sound : forall s a, aeval s (simplif_aexp a) = aeval s a := by
  intro s a
  induction a
  any_goals grind [mk_PLUS_sound, mk_MINUS_sound]

@[grind] def mk_EQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | .CONST n1, .CONST n2 => if n1 = n2 then .TRUE else .FALSE
  | .PLUS a1 (.CONST n1), .CONST n2 => .EQUAL a1 (.CONST (n2 - n1))
  | _, _ => .EQUAL a1 a2

@[grind] def mk_LESSEQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | .CONST n1, .CONST n2 => if n1 <= n2 then .TRUE else .FALSE
  | .PLUS a1 (.CONST n1), .CONST n2 => .LESSEQUAL a1 (.CONST (n2 - n1))
  | _, _ => .LESSEQUAL a1 a2

@[grind] def mk_NOT (b: bexp) : bexp :=
  match b with
  | .TRUE => .FALSE
  | .FALSE => .TRUE
  | .NOT b => b
  | _ => .NOT b

@[grind] def mk_AND (b1 b2: bexp) : bexp :=
  match b1, b2 with
  | .TRUE, _ => b2
  | _, .TRUE => b1
  | .FALSE, _ => .FALSE
  | _, .FALSE => .FALSE
  | _, _ => .AND b1 b2

theorem mk_EQUAL_sound:
  forall s a1 a2, beval s (mk_EQUAL a1 a2) = (aeval s a1 = aeval s a2) := by
    intro s a1 a2
    fun_cases (mk_EQUAL a1 a2) <;> grind

theorem mk_LESSEQUAL_sound:
  forall s a1 a2, beval s (mk_LESSEQUAL a1 a2) = (aeval s a1 <= aeval s a2) := by
    intro s a1 a2
    fun_cases mk_LESSEQUAL a1 a2 <;> grind

theorem mk_NOT_sound :
  forall s b, beval s (mk_NOT b) = ¬ (beval s b) := by
    intros s b
    fun_cases (mk_NOT b) <;> grind

theorem mk_AND_sound:
  forall s b1 b2, beval s (mk_AND b1 b2) = (beval s b1 ∧ beval s b2) := by
    intro s b1 b2
    fun_cases mk_AND b1 b2
    any_goals grind

@[grind] def mk_IFTHENELSE (b: bexp) (c1 c2: com) : com :=
  match b with
  | .TRUE => c1
  | .FALSE => c2
  | _ => .IFTHENELSE b c1 c2

@[grind] def mk_WHILE (b: bexp) (c: com) : com :=
  match b with
  | .FALSE => .SKIP
  | _ => .WHILE b c

theorem cexec_mk_IFTHENELSE: forall s1 b c1 c2 s2,
  cexec s1 (if beval s1 b then c1 else c2) s2 ->
  cexec s1 (mk_IFTHENELSE b c1 c2) s2 := by
    intro s1 b c1 c2 s2
    fun_cases (mk_IFTHENELSE b c1 c2) <;> grind

theorem cexec_mk_WHILE_done: forall s1 b c,
  beval s1 b = false ->
  cexec s1 (mk_WHILE b c) s1 := by
    intro s1 b c H
    fun_cases mk_WHILE b c <;> grind

theorem cexec_mk_WHILE_loop: forall b c s1 s2 s3,
  beval s1 b = true -> cexec s1 c s2 -> cexec s2 (mk_WHILE b c) s3 ->
  cexec s1 (mk_WHILE b c) s3 := by
    intro b c s1 s2 s3 h1 h2 h3
    fun_cases (mk_WHILE b c) <;> grind
