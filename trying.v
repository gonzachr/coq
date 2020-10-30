Inductive knat : Type :=
| O
| P (n : knat) (m : knat).

Check (P O) O.
