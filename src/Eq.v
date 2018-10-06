Class Eq (A : Type) := {
  eqb  : A -> A -> bool
}.

Infix "==" := eqb (at level 40).
(* Infix "/=" := neqb (at level 40). *)