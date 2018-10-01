Require Import Data.Functor.

Inductive Maybe (A : Type) : Type :=
| Nothing : Maybe A
| Just : A -> Maybe A.

Arguments Nothing {A}.
Arguments Just {A} _.

(* Notation Maybe   := option. *)
(* Notation Nothing := None. *)
(* Notation Just    := Some. *)

Definition fromMaybe {A : Type} (x : A) (my : Maybe A) : A :=
  match my with
 | Just z  => z
 | Nothing => x
  end.

Definition maybe {A B : Type} `(x : B) `(f : A -> B) (my : Maybe A) : B :=
  match my with
 | Just z  => f z
 | Nothing => x
  end.

Definition Maybe_map {A B : Type} `(f : A -> B) (x : Maybe A) : Maybe B :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.