import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

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

def Store := Std.HashMap ident Int
@[grind] def matches' (s: store) (S: Store): Prop :=
  forall x n, S.get? x = .some n -> s x = n

@[grind] def Le (S1 S2: Store) : Prop :=
  forall x n, S2.get? x = .some n -> S1.get? x = .some n

@[grind] def Top : Store := Std.HashMap.emptyWithCapacity

@[grind] def Join (S1 S2: Store) : Store :=
  S1.filter (fun key _ => S2.get? key == S1.get? key)

-- In leroy's course this is decidable
def Equal (S1 S2: Store) := Std.HashMap.Equiv S1 S2

def Equal' (S1 S2 : Store) : Bool := S1.toArray.all (S2.toArray.contains) && S2.toArray.all (S1.toArray.contains)


-- (** We show the soundness of these lattice operations with respect to
--   the [matches] and the [Le] relations. *)

theorem matches_Le: forall s S1 S2, Le S1 S2 -> matches' s S1 -> matches' s S2 := by
  intro s S1 S2 h1 h2
  grind

theorem Le_Top: forall S, Le S Top := by
  intro S
  grind [Std.HashMap]

@[grind] theorem Join_characterization:
forall S1 S2 x n,
  (Join S1 S2).get? x = .some n ↔
  S1.get? x = .some n ∧ S2.get? x = .some n := by
  intro S1 S2 x n
  constructor
  case mpr =>
    grind
  case mp =>
    sorry

theorem Le_Join_l: forall S1 S2, Le S1 (Join S1 S2) := by intros; grind

theorem  Le_Join_r: forall S1 S2, Le S2 (Join S1 S2) := by intros; grind

theorem Equal_Le: forall S1 S2, Equal S1 S2 -> Le S1 S2 := by
  intro S1 S2 eq
  unfold Equal at eq
  unfold Le
  intro x n
  have := @Std.HashMap.Equiv.getElem?_eq _ _ _ _ S1 S2 _ _ x eq
  grind

@[grind] def lift1 {A B: Type} (f: A -> B) (o: Option A) : Option B :=
  match o with
  | .some x => .some (f x)
  | .none => .none

@[grind] def lift2 {A B C: Type} (f: A -> B -> C) (o1: Option A) (o2: Option B) : Option C :=
  match o1, o2 with
  | .some x1, .some x2 => .some (f x1 x2) | _, _ => .none

@[grind] def Aeval (S: Store) (a: aexp) : Option Int :=
  match a with
  | .CONST n => .some n
  | .VAR x => S.get? x
  | .PLUS a1 a2 => lift2 (Int.add) (Aeval S a1) (Aeval S a2)
  | .MINUS a1 a2 => lift2 (Int.sub) (Aeval S a1) (Aeval S a2)

@[grind] def Beval (S: Store) (b: bexp) : Option Bool :=
  match b with
  | .TRUE => .some true
  | .FALSE => .some false
  | .EQUAL a1 a2 => lift2 (fun m n => m == n) (Aeval S a1) (Aeval S a2)
  | .LESSEQUAL a1 a2 => lift2 (fun m n => m <= n) (Aeval S a1) (Aeval S a2)
  | .NOT b1 => lift1 (fun m => !m) (Beval S b1)
  | .AND b1 b2 => lift2 (fun m n => m && n) (Beval S b1) (Beval S b2)

@[grind] theorem Aeval_sound:
  forall s S, matches' s S ->
  forall a n, Aeval S a = .some n -> aeval s a = n := by
    intro s S h1 a n h2
    induction a generalizing n
    any_goals grind
    case PLUS a1 a2 a1_ih a2_ih =>
      simp [Aeval] at h2
      unfold lift2 at h2
      split at h2 <;> grind
    case MINUS a1 s2 a1_ih a2_ih =>
      simp [Aeval] at h2
      unfold lift2 at h2
      split at h2 <;> grind

theorem Beval_sound:
  forall s S, matches' s S ->
  forall b n, Beval S b = .some n -> beval s b = n := by
    intro s S h1 b n h2
    induction b generalizing n
    any_goals grind
    case EQUAL a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2
      any_goals grind
    case LESSEQUAL a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2 <;> grind
    case NOT a1 a1_ih =>
      unfold Beval at h2
      unfold lift1 at h2
      split at h2 <;> grind
    case AND a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2 <;> grind


@[grind] def Update (x: ident) (N: Option Int) (S: Store) : Store :=
  match N with
  | .none => S.erase x
  | .some n => S.insert x n

@[grind] theorem update_characterisation : forall S x N y,
  (Update x N S).get? y = if x == y then N else S.get? y := by
    intro S x N y
    simp
    split
    case isTrue eq =>
      simp at eq
      rw [eq]
      unfold Update
      grind
    case isFalse neq =>
      simp at neq
      unfold Update
      grind

theorem matches_update: forall s S x n N,
  matches' s S ->
  (forall i, N = .some i -> n = i) ->
  matches' (update x n s) (Update x N S) := by
    intro s S x n N m h
    grind

def fixpoint_rec (F: Store -> Store) (fuel: Nat) (S: Store) : Store :=
  match fuel with
  | 0 => Top
  | fuel + 1 =>
      let S' := F S
      if Equal' S' S then S else fixpoint_rec F fuel S'


-- (** Let's say that we will do at most 20 iterations. *)

-- Definition num_iter := 20%nat.

-- Definition fixpoint (F: Store -> Store) (init_S: Store) : Store :=
--   fixpoint_rec F num_iter init_S.

-- (** The result [S] of [fixpoint F] is sound, in that it satisfies
--     [F S <= S] in the lattice ordering. *)

-- Lemma fixpoint_sound: forall F init_S,
--   let S := fixpoint F init_S in Le (F S) S.
-- Proof.
--   intros F.
--   assert (A: forall fuel S,
--              fixpoint_rec F fuel S = Top
--              \/ Equal (F (fixpoint_rec F fuel S)) (fixpoint_rec F fuel S) = true).
--   { induction fuel as [ | fuel]; cbn; intros.
--   - auto.
--   - destruct (Equal (F S) S) eqn:E.
--     + auto.
--     + apply IHfuel.
--   }
--   intros.
--   assert (E: S = Top \/ Equal (F S) S = true) by apply A.
--   destruct E as [E | E].
--   - rewrite E.  apply Le_Top.
--   - apply Equal_Le; auto.
-- Qed.

-- (** Now we can analyze commands by executing them "in the abstract".
--   Given an abstract store [S] that represents what we statically know
--   about the values of the variables before executing command [c],
--   [cexec'] returns an abstract store that describes the values of
--   the variables after executing [c]. *)

-- Fixpoint Cexec (S: Store) (c: com) : Store :=
--   match c with
--   | SKIP => S
--   | ASSIGN x a => Update x (Aeval S a) S
--   | SEQ c1 c2 => Cexec (Cexec S c1) c2
--   | IFTHENELSE b c1 c2 =>
--       match Beval S b with
--       | Some true => Cexec S c1
--       | Some false => Cexec S c2
--       | None => Join (Cexec S c1) (Cexec S c2)
--       end
--   | WHILE b c1 =>
--       fixpoint (fun x => Join S (Cexec x c1)) S
--   end.

-- (** The soundness of the analysis follows. *)

-- Ltac inv H := inversion H; clear H; subst.

-- Lemma Cexec_sound:
--   forall c s1 s2 S1,
--   cexec s1 c s2 -> matches s1 S1 -> matches s2 (Cexec S1 c).
-- Proof.
--   induction c; intros s1 s2 S1 EXEC AG; cbn [Cexec].
-- - (* SKIP *)
--   inv EXEC. auto.
-- - (* ASSIGN *)
--   inv EXEC. apply matches_update. auto. apply Aeval_sound. auto.
-- - (* SEQ *)
--   inv EXEC. apply IHc2 with s'; auto. apply IHc1 with s1; auto.
-- - (* IFTHENELSE *)
--   inv EXEC.
--   destruct (Beval S1 b) as [[]|] eqn:BE.
--   + erewrite Beval_sound in H4 by eauto. apply IHc1 with s1; auto.
--   + erewrite Beval_sound in H4 by eauto. apply IHc2 with s1; auto.
--   + destruct (beval s1 b).
--     * eapply matches_Le. apply Le_Join_l. eapply IHc1; eauto.
--     * eapply matches_Le. apply Le_Join_r. eapply IHc2; eauto.
-- - (* WHILE *)
--   set (F := fun x => Join S1 (Cexec x c)).
--   set (X := fixpoint F S1).
--   assert (INNER: forall s1 c1 s2,
--                  cexec s1 c1 s2 ->
--                  c1 = WHILE b c ->
--                  matches s1 X ->
--                  matches s2 X).
--   { induction 1; intros EQ AG1; inv EQ.
--   - (* WHILE stop *)
--     auto.
--   - (* WHILE loop *)
--     apply IHcexec2; auto.
--     unfold X. eapply matches_Le. apply fixpoint_sound.
--     unfold F. eapply matches_Le. apply Le_Join_r.
--     apply IHc with s. auto. fold F. fold X. auto.
--   }
--   eapply INNER; eauto.
--   unfold X. eapply matches_Le. apply fixpoint_sound.
--   unfold F. eapply matches_Le. apply Le_Join_l.
--   auto.
-- Qed.



-- (** ** 8.3 The constant propagation optimization *)

-- (** We can use the results of the static analysis to simplify expressions
--   further, replacing variables with known values by these values, then
--   applying the smart constructors. *)

-- Fixpoint cp_aexp (S: Store) (a: aexp) : aexp :=
--   match a with
--   | CONST n => CONST n
--   | VAR x => match IdentMap.find x S with Some n => CONST n | None => VAR x end
--   | PLUS a1 a2 => mk_PLUS (cp_aexp S a1) (cp_aexp S a2)
--   | MINUS a1 a2 => mk_MINUS (cp_aexp S a1) (cp_aexp S a2)
--   end.

-- Fixpoint cp_bexp (S: Store) (b: bexp) : bexp :=
--   match b with
--   | TRUE => TRUE
--   | FALSE => FALSE
--   | EQUAL a1 a2 => mk_EQUAL (cp_aexp S a1) (cp_aexp S a2)
--   | LESSEQUAL a1 a2 => mk_LESSEQUAL (cp_aexp S a1) (cp_aexp S a2)
--   | NOT b => mk_NOT (cp_bexp S b)
--   | AND b1 b2 => mk_AND (cp_bexp S b1) (cp_bexp S b2)
--   end.

-- (** Under the assumption that the concrete store matchess with the abstract store,
--   these optimized expressions evaluate to the same values as the original
--   expressions. *)

-- Lemma cp_aexp_sound:
--   forall s S, matches s S ->
--   forall a, aeval s (cp_aexp S a) = aeval s a.
-- Proof.
--   intros s S AG; induction a; cbn.
-- - auto.
-- - destruct (IdentMap.find x S) as [n|] eqn:FIND.
--   + symmetry. apply AG. auto.
--   + auto.
-- - rewrite mk_PLUS_sound, IHa1, IHa2. auto.
-- - rewrite mk_MINUS_sound, IHa1, IHa2. auto.
-- Qed.

-- Lemma cp_bexp_sound:
--   forall s S, matches s S ->
--   forall b, beval s (cp_bexp S b) = beval s b.
-- Proof.
--   intros s S AG; induction b; cbn.
-- - auto.
-- - auto.
-- - rewrite mk_EQUAL_sound, ! cp_aexp_sound by auto. auto.
-- - rewrite mk_LESSEQUAL_sound, ! cp_aexp_sound by auto. auto.
-- - rewrite mk_NOT_sound, IHb. auto.
-- - rewrite mk_AND_sound, IHb1, IHb2. auto.
-- Qed.

-- (** The optimization of commands consists in propagating constants
--   in expressions and simplifying the expressions, as above.
--   In addition, conditionals and loops whose conditions are statically
--   known will be simplified too, thanks to the smart constructors.

--   The [S] parameter is the abstract store "before" the execution of [c].
--   When recursing through [c], it must be updated like the static analysis
--   [Cexec] does.  For example, if [c] is [SEQ c1 c2], [c2] is optimized
--   using [Cexec S c1] as abstract store "before".  Likewise, if
--   [c] is a loop [WHILE b c1], the loop body [c1] is optimized using
--   [Cexec S (WHILE b c1)] as the abstract store "before".
-- *)

-- Fixpoint cp_com (S: Store) (c: com) : com :=
--   match c with
--   | SKIP => SKIP
--   | ASSIGN x a =>
--       ASSIGN x (cp_aexp S a)
--   | SEQ c1 c2 =>
--       SEQ (cp_com S c1) (cp_com (Cexec S c1) c2)
--   | IFTHENELSE b c1 c2 =>
--       mk_IFTHENELSE (cp_bexp S b) (cp_com S c1) (cp_com S c2)
--   | WHILE b c =>
--       let sfix := Cexec S (WHILE b c) in
--       mk_WHILE (cp_bexp sfix b) (cp_com sfix c)
--   end.

-- (** Example: let's "optimize" Euclidean division under the dubious assumption
--   that the divisor is 0... *)

-- Compute (cp_com (Update "b" (Some 0) Top) Euclidean_division).

-- (** Result is (in pseudocode):
-- <<
--      r := a;
--      q := 0;
--      while 0 <= r do
--        r := r; q := q + 1
--      done
-- >>
-- *)

-- (** The proof of semantic preservation needs an unusual induction pattern:
--   structural induction on the command [c], plus an inner induction
--   on the number of iterations if [c] is a loop [WHILE b c1].
--   This pattern follows closely the structure of the abstract interpreter
--   [Cexec]: structural induction on the command + local fixpoint for loops. *)

-- Lemma cp_com_correct_terminating:
--   forall c s1 s2 S1,
--   cexec s1 c s2 -> matches s1 S1 -> cexec s1 (cp_com S1 c) s2.
-- Proof.
--   induction c; intros s1 s2 S1 EXEC AG; cbn [cp_com].
-- - (* SKIP *)
--   auto.
-- - (* ASSIGN *)
--   inv EXEC. replace (aeval s1 a) with (aeval s1 (cp_aexp S1 a)).
--   apply cexec_assign.
--   apply cp_aexp_sound; auto.
-- - (* SEQ *)
--   inv EXEC. apply cexec_seq with s'.
--   apply IHc1; auto.
--   apply IHc2; auto. apply Cexec_sound with s1; auto.
-- - (* IFTHENELSE *)
--   inv EXEC.
--   apply cexec_mk_IFTHENELSE.
--   rewrite cp_bexp_sound by auto.
--   destruct (beval s1 b); auto.
-- - (* WHILE *)
--   set (X := Cexec S1 (WHILE b c)).
--   assert (INNER: forall s1 c1 s2,
--                  cexec s1 c1 s2 ->
--                  c1 = WHILE b c ->
--                  matches s1 X ->
--                  cexec s1 (mk_WHILE (cp_bexp X b) (cp_com X c)) s2).
--   { induction 1; intros EQ AG1; inv EQ.
--   - (* WHILE stop *)
--     apply cexec_mk_WHILE_done. rewrite cp_bexp_sound by auto. auto.
--   - (* WHILE loop *)
--     apply cexec_mk_WHILE_loop with s'. rewrite cp_bexp_sound by auto. auto.
--     apply IHc; auto.
--     apply IHcexec2; auto.
--     unfold X. cbn [Cexec].
--     eapply matches_Le. apply fixpoint_sound.
--     eapply matches_Le. apply Le_Join_r.
--     apply Cexec_sound with s; auto.
--   }
--   eapply INNER; eauto.
--   unfold X. cbn [Cexec].
--   eapply matches_Le. apply fixpoint_sound.
--   eapply matches_Le. apply Le_Join_l. auto.
-- Qed.
