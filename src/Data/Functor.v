Generalizable All Variables.

Class Functor (F : Type -> Type) : Type :=
  { fmap : forall {A B : Type}, (A -> B) -> F A -> F B}.

Arguments fmap {F _ A B} g x.

Infix "<$>" := fmap (at level 28, left associativity, only parsing).