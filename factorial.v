Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => (mult n (factorial n'))
  end.

Compute (factorial 5).
