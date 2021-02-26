Module NatList.

Require Import Bool.

Check Bool.le.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 1 2).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 1 2)).
Compute (snd (pair 1 2)).

Notation "( x , y )" := (pair x y).

Compute (1, 2).

Compute (fst (1,2)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Compute (fst' (1,2)).

Definition swap_pair (p: natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Compute (swap_pair (1,2)).

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros. destruct p as [n m]. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p as [n m]. simpl. reflexivity. Qed.
                                
Theorem fst_swap_is_snd : forall (p: natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Check mylist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Check [1;2;3].

Check 1 :: [1].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute (repeat 1 2).

Fixpoint length (l : natlist) : nat :=
  match l with
  | h :: t => S (length t)
  | nil => O
  end.

Compute length [1;2;3].

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | h :: t  => h :: app t l2
  | nil => l2
  end.

Compute (app [1;2] [3;4]).

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Compute [1;2] ++ [3;4].

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | h :: t => h
  | nil => default
  end.

Compute hd 0 [1;2;3].

Definition tl (l : natlist) : natlist :=
  match l with
  | h :: t => t
  | nil => nil
  end.

Compute tl [1;2;3].

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | h :: t => match h with
              | O => nonzeros t
              | S h' => S h' :: nonzeros t
              end
  | nil => nil
  end.

  
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.                
  intros. simpl. reflexivity. Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | S (S n') => evenb n'
  | S n' => false
  | O => true
  end.

Compute (evenb 2).
Compute (evenb 1).
                      
Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | h :: t => match evenb h with
              | false => h :: oddmembers t
              | true => oddmembers t
              end
  | nil => nil
  end.

Compute oddmembers [0;1;0;2;3;0;0].


Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat :=
  match l with
  | nil => O
  | _ => length (oddmembers l)
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  | nil, l2' => l2'
  | l1', nil => l1'
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
 alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4;5] = [1;4;2;5;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | S m', S n' => eqb m' n'
  | O, O => true
  | _, _ => false
  end.


Compute (eqb 2 2).

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | h :: t => match (eqb h v) with
                | true => S (count v t)
                | false => count v t
              end
  | nil => O
  end.


Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := (sum [v] s).

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match (count v s) with
    | S n' => true
    | O => false
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match (member v s) with
  | true => match s with
            | h :: t => match (eqb v h) with
                          | true => t
                          | false => h :: (remove_one v t)
                        end
            | nil => nil
            end
  | false => s
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Example test_remove_one5:
  remove_one 5 nil = nil.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match (member v s) with
      | true => match s with
                | h :: t => match (eqb v h) with
                              | true => remove_all v t
                              | false => h :: remove_all v t
                            end
                | nil => nil
                end
      | false => s
end.

Example test_member_nil: member 1 nil = false.
Proof. reflexivity. Qed.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint ltb (m n : nat) : bool :=
  match m, n with
   | S m', S n' => ltb m' n'
   | O, S n' => true
   | O, O => true
   | _, _ => false
  end.



Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | h :: t => match (ltb (count h s1) (count h s2)) with
                | true => (subset t s2)
                | fale => false
              end
  | nil => true
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* Theorem bag_theorem : forall (s : bag) (n : nat),
    count n (add n s) = (count n s) + 1.
Proof.
  intros.
  - destruct n as [| n'] eqn:E1.
    + simpl. reflexivity.
    + assert (H: (add (S n')[ ]) = [S n']).
      { reflexivity. }
      rewrite H.
      assert (H1: (count (S n') [ ] + 1) = 1).
      { simpl. reflexivity. }
      rewrite H1.
      assert (H2: forall (m : nat), (count (m) [m] = 1)).
      { intros. induction m as [| m' Hm']. reflexivity.
        rewrite <- Hm'. reflexivity. }
     rewrite H2. reflexivity.
    + rewrite <- E. admit. *)

(*Theorem bag_theorem : forall (v : nat) (s : bag),
    count v (add v s) = 1 + count v s.
Proof.
  intros.
  assert (H : add v s = v :: s).
  { reflexivity . }
  destruct s as [| h t].*)

Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof.
  reflexivity.
Qed.

Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
Proof.
  intros. destruct l as [| n l'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
 intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
 - reflexivity.
 - simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => l
    | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem plus_0 : forall n : nat,
    n + 0 = n.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_n_Sm : forall m n : nat,
    S (n + m) = n + S m.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem nat_comm : forall m n : nat,
    m + n = n + m.
Proof.
  intros. induction m as [| m' IHm'].
  - simpl. rewrite plus_0. reflexivity.
  - simpl. rewrite IHm'. rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite app_length. simpl.
    rewrite nat_comm. rewrite IHl'. reflexivity.
Qed.                                                      
                            
Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.


Search ((?x ++ ?y) ++ ?z = ?x ++ ?y ++ ?z).


Theorem rev_app_distr : forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - destruct n as [| n'].
     + simpl. rewrite IHl1'. reflexivity.
     + simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | nil, nil => true
    | h :: t, h2 :: t2 => (andb (eqb h h2) (eqblist t t2))
    | _, _ => false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l : natlist,
    true = eqblist l l.
Proof.
  intros. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. induction n as [| n' IHn'].
    + reflexivity.
    + simpl. rewrite <- IHn'. reflexivity.
Qed.    

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | S n', S m' => leb n' m'
  | 0, S m' => true
  | S n', 0 => false
  | 0, 0 => true
  end.

Compute (leb 2 1).

Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. 
