Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, S m' => false
  | S n', O => false
  | O, O => true
  | S n', S m' => eqb n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem zero_nbeq_plus_q : forall n : nat,
    0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
