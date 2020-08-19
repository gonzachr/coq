Theorem peano_3 : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros. destruct n as [|n'] eqn:En.
  - destruct m as [|m'] eqn:Em.
    + reflexivity.
    + rewrite <- H. reflexivity.
  - rewrite H. reflexivity.
Qed.
