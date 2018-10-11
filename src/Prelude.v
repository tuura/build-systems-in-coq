Class Eq (A : Type) := {
  eqb  : A -> A -> bool
}.

Infix "==" := eqb (at level 40).
(* Infix "/=" := neqb (at level 40). *)

Definition undefined {a : Type} : a. Admitted.

Definition const {A B : Type} (x : A) (y : B) : A := x.

Fixpoint eq_nat_impl n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat_impl n1 m1
  end.

Instance eq_nat : Eq nat := { eqb := eq_nat_impl}.