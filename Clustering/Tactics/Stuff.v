Require Import Clustering.Tactics.LibTactics.
Set Implicit Arguments.

Ltac crunch_destruct V :=
 repeat (match goal with
  | [ |- context [ V ?X          ] ] => destruct (V X)
  | [ |- context [ V ?X ?Y       ] ] => destruct (V X Y)
  | [ |- context [ V ?X ?Y ?Z    ] ] => destruct (V X Y Z)
  | [ |- context [ V ?X ?Y ?Z ?U ] ] => destruct (V X Y Z U)
  end).

Ltac bye_not_eq :=
 try solve
 [ substs;
   match goal with
    H : ?x <> ?x |- _
    => destruct H; reflexivity
   end].
