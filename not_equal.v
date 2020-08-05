Theorem test1 : ~ 1 = 2.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.
