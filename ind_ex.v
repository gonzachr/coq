Theorem n_m1_plus_k : forall n k : nat,
    n * (1 + k) = n + n * k.
Proof.
  intros. simpl. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.
    assert (H: k + (n' + n' * k) = n' + (k + n' * k)).
    { + rewrite -> plus_comm.


    }


Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
  
