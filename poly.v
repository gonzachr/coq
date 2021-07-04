Inductive list (X : Type) : Type :=
  | nil 
  | cons (x : X) (l : list X).

Definition natlist := cons nat.
Definition boollist := cons bool.

Check natlist 1 (nil nat).
Check boollist true (nil bool).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
    | O => nil X
    | S count' => cons X x (repeat X x count')
  end.

Example test_repeat :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof.
  reflexivity.
Qed.
  
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof.
  reflexivity.
Qed.

Module MumbleGrumble.


Inductive mumble : Type :=
| a
| b (x : mumble) (y : nat)
| c.

Inductive grumble (X : Type) : Type :=
| d (m : mumble)
| e (x : X).
     
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.

Fixpoint repeat'' X x count : list X :=
  match count with
    | 0 => nil _ 
    | S count' => cons _ x (repeat'' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check list123''.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X : Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2 
    | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Eval compute in rev (cons 2 (cons 1 nil)).

Fixpoint length {X: Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length t)
  end.

Eval compute in length (cons 1 (cons 2 nil)).

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X : Type), forall l : list X,
      l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
 Qed.

Theorem app_assoc : forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.
  
Lemma app_length : forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1 as [| n l1' IHl1'].
  - rewrite app_nil_r. simpl. reflexivity.
  - simpl. rewrite IHl1'. rewrite <- app_assoc. reflexivity.
Qed.
    
Theorem rev_involutive : forall X : Type, forall l : list X,
      rev (rev l) = l.
Proof.
  intros. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity.
Qed.


Inductive prod (X Y : Type) : Type :=
 | pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition scn {X Y : Type} (p: X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []               
  | x :: tx, y :: ty => (x,y)  :: (combine tx ty)
  end.

Compute combine [1;2;3] [true;false;false;true].
               
 
Check @combine.



