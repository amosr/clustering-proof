Require Import Clustering.ILP.Base.
Require Import Clustering.ILP.Linear.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Notation "x |+| y" := (plus x y)
 (at level 50, left associativity).

Notation "x |* y" := (mul x y)
 (at level 40).

Notation "x *| y" := (mul y x)
 (at level 40).

Notation "a |<=| b" := [Le a b]
  (at level 70, no associativity).
Notation "a |==| b" := [Le a b; Le b a]
  (at level 70, no associativity).
Notation "a |>=| b" := [Le b a]
  (at level 70, no associativity).
Notation "a |<| b" := [Le a (b |+| const _ (- 1))]
  (at level 70, no associativity).
Notation "a |>| b" := [Le b (a |+| const _ (- 1))]
  (at level 70, no associativity).

Notation "a |<=| b |<=| c" := ((a |<=| b) ++ (b |<=| c))
  (at level 70, b at next level).
Notation "a |<| b |<| c" := ((a |<| b) ++ (b |<| c))
  (at level 70, b at next level).
Notation "a |>=| b |>=| c" := ((a |>=| b) ++ (b |>=| c))
  (at level 70, b at next level).
Notation "a |>| b |>| c" := ((a |>| b) ++ (b |>| c))
  (at level 70, b at next level).

Definition constrs {A} (a : list (list (C A))) : list (C A)
 := fold_right (fun x y => x ++ y) [] a.

(*
Inductive V := V_x | V_y.

Definition x := constrs
  [ const _ 1 |+| const _ 2 |+| var 1 V_x |<=| const _ 1
  ; const _ 1 |<=| var1 V_x |<=| const _ 5].
Print x.
Eval compute in x.
*)
