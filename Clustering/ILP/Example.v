Require Import Clustering.ILP.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Inductive V
  := V_x 
   | V_y.

Definition Objective : Linear V := var 1 V_x |+| var 2 V_y.

Definition Constraints : list (C V) :=
  constrs
  [ var1 V_x |==| var1 V_y
  ; const _ 1 |<=| var1 V_y ].

Definition Sat := fun x => match x with | V_x => 5 | V_y => 5 end.


Lemma Sat_Valid: Valid Constraints Sat.
Proof.
 validate; simpl; omega.
Qed.



Lemma x_eq_y : forall a, Valid Constraints a -> a V_x = a V_y.
Proof.
 intros.
 crunch_valid H.
 simpl in *.
 omega.
Qed.


Lemma y_gt_1 : forall a, Valid Constraints a -> a V_y >= 1.
Proof.
 intros.
 crunch_valid H.
 simpl in *.
 omega.
Qed.


Definition Min := MinimalExists Objective Sat_Valid.


Lemma min : forall a, assignmentOfMinimal Min = a
  -> a V_x = 1 \/ a V_y = 1.
Proof.
 intros.
 destruct Min.
 simpl in H. subst.
 assert (a V_x = a V_y).
   apply x_eq_y; eauto.

 assert (a V_y >= 1).
  apply y_gt_1. eauto.

 assert (a V_y = 1).
   simpl in l.

   remember ((fun x => match x with | V_x => 1 | V_y => 1 end) : Assignment V) as b.
   assert (Valid Constraints b) as ValB.
      subst.
      validate; simpl; omega.

   apply l in ValB.
    subst.
    simpl in ValB.
 omega.
 omega.
Qed.


