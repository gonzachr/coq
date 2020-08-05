Module NatPlayground.
  
Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

Inductive nat : Type :=
| O
| S (n : nat).

Check (S(S O)).

Inductive nat' : Type :=
| stop
| tick (foo : nat').

Definition pred (n : nat) : nat :=
 match n with
 | O => O
 | S n' => n'
 end.

Compute (pred (S(S O))).

End NatPlayground.

Check (S(S(S O))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.
