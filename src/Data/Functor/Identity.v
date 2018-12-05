Inductive Identity A := Id : A -> Identity A.

Definition getIdentity {A : Type} (a : Identity A) :=
  match a with
  | Id _ x => x
  end.