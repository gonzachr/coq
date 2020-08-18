Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', O => false
  | O, S m' => false
  | S n', S m' => (eqb n' m')
  end.

Fixpoint eqb_alt (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S n' => false
         end
  | S n' => match m with
            | O => false
            | S m' => (eqb_alt n' m')
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, S m' => true
  | S n', O => false
  | S n', S m' => (leb n' m')
  | O, O => true
  end.


Example leg_q: (leb 1 1) = true.
Proof. simpl. reflexivity. Qed.
Example leg_q_1: (leb 0 1) = true.
Proof. simpl. reflexivity. Qed.
Example leg_q_2: (leb 1 0) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Example eqb_1: (eqb 1 1) = true.
Proof. simpl. reflexivity. Qed.

Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | S n', O => false
  | O, S m' => true
  | O, O => false
  | S n', S m' => (ltb n' m')
  end.

Definition minus (n m : nat) : nat :=
  match n,m with
  | O, _ => O
  | _, O => n
  | S n', S m' => (minus n' m')
  end.

Compute (minus 1 2).

Definition ltb_alt (n m : nat) : bool :=
  match n, m with
  | _, O => false
  | O, S m' => true
  | S n', S m' => match (minus (S m') (S n')) with
                 | O => false
                 | S p' => true
                  end
  end.


Example test_ltb1: (ltb_alt 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb_alt 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb_alt 4 2) = false.
Proof. simpl. reflexivity. Qed.

