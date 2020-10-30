
Compute S O.

Fixpoint add (m: nat) (n: nat) : nat :=
  match m with
    | S m' => S (add m' n)
    | O => n
  end.

Theorem plus_O_n: forall n:nat,
    n = 0 + n.
Proof.
  reflexivity.
Qed.           

Theorem plus_n_O: forall n:nat,
    n = n + 0.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint minus (m: nat) (n: nat) : nat :=
  match m, n with
      | S m', S n' => (minus m' n')
      | S m', O => S m'
      | O, _ => O
  end.

Compute (minus 4 1).

Theorem minus_n_n : forall n,
    minus n n = 0.
Proof.
  intros. induction n as [| n' IHn']. 
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint mult (m:nat) (n:nat) : nat :=
  match m with
   | O => O
   | S m' => (mult m' n) + n
  end.


Theorem mult_0_r : forall n:nat,
    (mult n 0) = 0.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (m:nat) : nat :=
  match m with
    | O => O
    | S m' => S (S (double m'))
    end.
     
Compute (double 0).

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Fixpoint evenb (m:nat) : bool :=
  match m with
  | (S (S m')) => (evenb m')
  | O => true
  | S m' => false
  end.

Compute (evenb 3).


Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl.
    assert (H: forall b,  b = negb (negb b)).
    { destruct b eqn:E.
      + reflexivity.
      + reflexivity.
    }
    rewrite <- H. reflexivity. 
Qed.


(* Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: m + n = n + m).

  { rewrite -> plus_comm. simpl.}
    rewrite -> H. reflexivity.
Qed. *)

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem S_plus_1 : forall n : nat, S n = n + 1.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem n_opposite : forall m n : nat, m + n = m + n -> m = m.
Proof.
  intros. reflexivity.
Qed.
 
Theorem n_mult_1_sumk : forall n k,
    n * (1 + k) = n + n * k.
Proof.
  intros. simpl. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. rewrite -> plus_assoc.
    assert (H : k + n' = n' + k).
    { rewrite -> plus_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.

Theorem mult_0_n : forall n,
    0 = n * 0.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.  

Theorem mult_comm : forall m n,
    m * n = n * m.
Proof.
  intros. induction n as [| n' IHn'].
  - rewrite <- mult_0_n. reflexivity.
  - simpl. rewrite n_mult_1_sumk. rewrite IHn'. reflexivity.
Qed.

Fixpoint eqb (m : nat) (n : nat) : bool :=
  match m, n with
  | S m', S n' => (eqb m' n')
  | O, O => true
  | _, _ => false     
  end.

Fixpoint leb (m : nat) (n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => (leb m' n')
  | O, S n' => true
  | _, _ => false
  end.

Theorem leb_refl : forall n : nat,
  true = (leb n n).
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_0 : forall n : nat,
    0 + n = n.
Proof.
  intros. destruct n as [| n'] eqn: E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
    (eqb 0 (S n)) = false.
Proof.
  reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
  intros. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_1 : forall n m p : nat,
    leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros. induction p as [| p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat,
    (eqb (S n) O) = false.
Proof.    
  intros. reflexivity.
Qed.

Theorem mult_1_1 : forall n : nat, 1 * n = n.
Proof.
  intros. simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Definition notb (b : bool) : bool :=
  match b with
   | true => false
   | false => true 
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Theorem all3_spec : forall b c : bool,
    orb (andb b c)
        (orb (negb b)
             (negb c))
    = true.
Proof.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n' IHn'].
  - destruct m as [| m'] eqn:E.
    + reflexivity.
    + reflexivity.
  - destruct m as [| m'] eqn:E.
    + simpl. rewrite IHn'. rewrite -> plus_assoc. reflexivity.
    + simpl. rewrite IHn'. simpl. rewrite plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
    true = eqb n n.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros. rewrite plus_assoc. rewrite plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  rewrite plus_comm. reflexivity.
Qed.

  
