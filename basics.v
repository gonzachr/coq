Require Import Coq.Lists.List.
Open Scope list_scope.
Import ListNotations.

Theorem silly1 : forall (n m : nat),
    n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Check [1].


Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Fixpoint odd (n : nat) : bool :=
    match n with
    | O => false
    | 1 => true
    | S (S n') => odd n'
    end.

Fixpoint even (n: nat) : bool :=
  match odd n with
  | true => false
  | false => true
  end.


Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true ->
    odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2. apply eq1. apply eq3.
Qed.  


Search rev.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros l l'. apply rev_alt.
  
