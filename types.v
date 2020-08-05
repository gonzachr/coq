Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.
    

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
               end.

Check bool.
Check andb.
Check false.
Check (andb true false).

Definition negb (b1: bool) : bool :=
  match b1 with
  | true => false
  | false => true
  end.

Check (negb false).

Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
end.

Compute (monochrome (primary red)).

Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | primary _ => false
  | black => false
  | white => false
  end.

Compute (isred (primary blue)).
