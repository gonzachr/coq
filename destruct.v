Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S n', S m' => (eqb n' m')
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.

Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

