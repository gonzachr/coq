Module NatDefs.
  
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat,  1 + n = S n.
Proof. intros. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intro. simpl. reflexivity. Qed.

Theorem plus_id_exampl : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    intros H0.
    rewrite -> H.
    rewrite -> H0.
    reflexivity.
  Qed.

Theorem mult_0_plus : forall n m : nat,
      ( 0 + n ) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Induction 

Fixpoint plusn (n m : nat) : nat :=
  match n, m with
  | O, _ => m
  | S n', O => n
  | S n', S m' => S (plusn n m')
  end.

Notation "x + y" := (plusn x y)
                      (at level 50, left associativity)
                      : nat_scope.

Theorem S_1_eq : forall n : nat,
    S n = n + 1.

Proof.
  intros.
  simpl. 

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
  intros.
  rewrite -> H.

End NatDefs.
