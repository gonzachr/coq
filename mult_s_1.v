Module NatDefs.


Theorem S_n_eq_add : forall n : nat,
    1 + n = S n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
    S n = m ->
    m * (1 + n) = m * m.
Proof.
  intros.
  rewrite S_n_eq_add.
  rewrite H.
  reflexivity.
Qed.
