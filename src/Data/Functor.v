Class Functor (F : Type -> Type) :=
  { fmap : forall {A B : Type}, (A -> B) -> F A -> F B}.