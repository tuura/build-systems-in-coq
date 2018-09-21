Class Functor (F : Type -> Type) :=
  { fmap : forall {A B : Type}, (A -> B) -> F A -> F B}.

Inductive Const (A B : Type) : Type :=
  mkConst : A -> Const A B.

Definition getConst {A B : Type} (c : Const A B) : A :=
  match c with
  | mkConst _ _ x => x
  end.

Instance Const_Functor {C : Type} : Functor (Const C) :=
  {
    fmap {A} {B} f c := match c with
                        | mkConst _ _ x => mkConst C B x
                        end
  }.

(* The Task abstraction *)
Record Task (C : (Type -> Type) -> Type) (K V : Type) :=
  mkTask {run : forall F `{C F}, ((K -> F V) -> F V)}.
Check run.

(* -- | Find the dependency of a functorial task. *)
(* dependency :: Task Functor k v -> k *)
(* dependency task = getConst $ run task Const *)
Definition dependency {K V: Type} (task : Task Functor K V) : K :=
  getConst ((run Functor K V task (Const K)) (mkConst K V)).
