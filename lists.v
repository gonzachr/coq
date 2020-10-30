Module NatList.

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
