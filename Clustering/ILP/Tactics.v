Require Import Clustering.ILP.Base.
Require Import Clustering.Tactics.

Require Import Coq.Lists.List.

Ltac validate
 := repeat
 (match goal with
  | [ |- Valid _ _ ]
  => constructor
  | [ |- Valid_go _ _]
  => constructor
  end).

Import ListNotations.


Ltac crunch_valid H
 := inverts H; repeat
 (match goal with
  | [ H : Valid_go _ _ |- _]
  => inverts H
  end); subst; Z_simp_all.

(*
Tactic Notation "crunch_valid" hyp(H)
Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.
*)