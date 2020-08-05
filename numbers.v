Module NatPlayground.
  
Inductive nat : Type :=
| O
| S : nat -> nat.

Check (S O).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Compute (pred(S(S O))).

End NatPlayground.

Check (S (S O)).

Definition minustwo (n: nat) : nat :=
  match n with
  | O => O
  | S O  => O
  | S (S n') => n'
end.

Compute (minustwo 10).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := (negb (evenb n)).

Compute (oddb 3).

Example test_oddb1: (oddb 1) = true.
Proof.
  unfold oddb.
  simpl.
  reflexivity.
Qed.

Example test_oddb2: (oddb 4) = false.
Proof.
  unfold oddb.
  simpl.
  reflexivity.
Qed.

Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match m with
    | O => n
    | S n' => S (plus n n')
    end.

  Definition pred' (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  

  Compute (plus 4   3).

  Fixpoint minus (n : nat) (m : nat) : nat :=
    match m with
    | O => n
    | S n' => pred (minus n n')
    end.

  Compute (minus 3 1).

  Fixpoint mult (n : nat) (m : nat) : nat :=
    match m with
    | O => O
    | S n' => (plus (mult n n') n)
    end.

  Compute (mult 3 2).
