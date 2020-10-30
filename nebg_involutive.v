Print negb.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros. destruct b as [|] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Print andb.
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:E.
  - destruct c eqn:E1.  
    + reflexivity.
    + reflexivity.
  - destruct c eqn:E1.
    + reflexivity.
    + reflexivity.    
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn: Eb.
  - destruct c eqn: Ec.
    { destruct d eqn: Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn: Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn: Ec.
    { destruct d eqn: Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn: Ed.
      - reflexivity.
      - reflexivity. }
Qed.
