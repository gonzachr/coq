Definition minus (m n : nat) : nat :=
  match m, n with
  | _, O => O
  | O, S n' => n
  | S m', S n' => (minus m' n')
  end.

Definition ltb (n m : nat) : bool :=
  match n, m with
  | _, O => false
  | O, S m' => true
  | S n' as p, S m' as q => match (minus q p) with
                            | O => false
                            | _ => true
                            end
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb4: (ltb 0 2) = true.
Proof. simpl. reflexivity. Qed.
