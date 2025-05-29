set_option grind.warning false
set_option grind.debug true

def α : Type := Unit × Unit

def p (_ : α) : Prop := False

/--
error: `grind` internal error, trying to assert equality
  c = (c.fst, c.snd)
with proof
  Eq.refl c
which has type
  c = c
which is not definitionally equal with `reducible` transparency setting}
-/
#guard_msgs in
example : p c → False := by grind
