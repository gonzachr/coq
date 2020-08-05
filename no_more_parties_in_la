Fixpoint evenb (n: nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Definition oddb (n: nat) : bool := (negb (evenb n)).

Example oddb1: oddb 2 = false.
Proof.
unfold oddb.
unfold negb.
simpl.
reflexivity.
Qed.