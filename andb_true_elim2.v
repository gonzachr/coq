Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c eqn:Ec.
  - reflexivity.
  - intros H. rewrite <- H. destruct b eqn: Eb.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
