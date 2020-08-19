Inductive bool : Set :=
| true
| false.

Lemma equality_of_functions_commutes:
  forall (f: bool->bool) x y,
    (f x) = (f y) -> (f y) = (f x).

Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.
