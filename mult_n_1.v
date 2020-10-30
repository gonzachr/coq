Print Nat.mul.

Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
  intros. simpl.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl. reflexivity.
Qed.
