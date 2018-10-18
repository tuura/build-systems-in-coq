Class Monoid (m : Type) := {
  mempty : m;
  mappend : m -> m -> m;
}.

Instance list_Monoid (A : Type) : Monoid (list A) := {
  mempty := nil;
  mappend xs ys := app xs ys
}.