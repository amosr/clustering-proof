Require Import Clustering.ILP.

Require Import Coq.Lists.List.
Set Implicit Arguments.

Inductive V
  := V_x 
   | V_y.

Definition Objective : list (L V) := Lv V_x 1 :: Lv V_y 2 :: nil.

Definition Constraints : list (C V) := Le (Lv V_x 1) (Lv V_y 1) :: Le (Lv V_y 1) (Lv V_x 1) :: Le (Lc _ 1) (Lv V_x 1) :: nil.

Definition Sat := fun x => match x with | V_x => 5 | V_y => 5 end.

Lemma Sat_Valid: Valid Constraints Sat.
Proof.
 repeat constructor.
Qed.


Lemma x_eq_y : forall a, Valid Constraints a -> a V_x = a V_y.
Proof.
 intros.
 inversion H.
 inversion H2.
 inversion H3.
 inversion H11.
 omega.
Qed.


Lemma y_gt_1 : forall a, Valid Constraints a -> a V_y >= 1.
Proof.
 intros.
 inversion H.
 inversion H2.
 inversion H3.
 inversion H11.
 inversion H12.
 inversion H20.
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
     repeat constructor.

   apply l in ValB.
    subst.
    simpl in ValB.
 omega.
 omega.
Qed.


