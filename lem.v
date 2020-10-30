Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | false => b2
  | true => true
  end.

Theorem lem : forall b : bool,
    (orb b (negb b)) = true.
Proof.
  intros. destruct b eqn: E.
  - simpl. reflexivity.
  - simpl. reflexivity.
End.
