Require Import Clustering.Tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.


Fixpoint selfcross_go {V} (x : V) (ys : list V) : list (V * V)
 := match ys with
    | []       => []
    | (y::ys') => (x, y) :: selfcross_go x ys'
    end.

Fixpoint selfcross {V} (xs : list V) : list (V * V)
 := match xs with
    | []       => []
    | (x::xs') => selfcross_go x xs' ++ selfcross xs'
    end.


Fixpoint cross_go {V} (x : V) (ys : list V) : list (V * V)
 := match ys with
    | []       => []
    | (y::ys') => (x, y) :: cross_go x ys'
    end.

Fixpoint cross {V} (xs ys : list V) : list (V * V)
 := match xs with
    | []       => []
    | (x::xs') => cross_go x ys ++ cross xs' ys
    end.


Lemma In_or_not: forall A (a : A) xs
     (Heqdec : forall (a b : A), a = b \/ a <> b),
      In a xs \/ ~ In a xs.
Proof.
 intros.
 induction xs; eauto.
  destruct (Heqdec a a0).
   - left. constructor. auto.
   - destruct IHxs.
      left. apply in_cons. assumption.
      right. unfold not. intros.
             inversion H1; eauto.
Qed.

Fixpoint Contains {A} (f : A -> bool) (xs : list A) :=
 match xs with
 | [] => false
 | x::xs' => match f x with
             | true => true
             | false => Contains f xs'
             end
 end.


Lemma Contains_is_in: forall A (a : A) xs
     (Heqdec : forall (a b : A), a = b \/ a <> b)
     (beq    : A -> A -> bool)
     (Heqdec : forall (a b : A), beq a b = true <-> a = b),
      Contains (beq a) xs = true <-> In a xs.
Proof.
 intros.
  induction xs.
   simpl. split.
   intros. inversion H.
   eauto.

  simpl.
   remember (Heqdec a a0) as Eq.
   destruct Eq; subst.
    assert (beq a0 a0 = true). apply Heqdec0. eauto.
   rewrite H. split; eauto.

   remember (beq a a0) as B.
   destruct B.
   symmetry in HeqB.
   apply Heqdec0 in HeqB.
   contradiction.

  destruct IHxs; split; eauto.
   intros. destruct H1.
   symmetry in H1. contradiction.
   eauto.
Qed.


Lemma selfcross_go__In: forall {A} (xs : list A) i j,
    In j xs ->
    In (i,j) (selfcross_go i xs).
Proof.
 induction xs; intros.
  inverts H.
 simpl in *.
 destruct~ H.
  left. subst~.
Qed.


Lemma selfcross__In: forall {A} (xs : list A) i j,
    i <> j  ->
    In i xs ->
    In j xs ->
    In (i,j) (selfcross xs) \/ In (j,i) (selfcross xs).
Proof.
 induction xs; intros.
  inverts H0.
 simpl in *.
 destruct~ H0; destruct~ H1; subst.
  contradiction.

 left.
  apply in_or_app.
  left.
  apply selfcross_go__In.
  assumption.

 right.
  apply in_or_app.
  left.
  apply selfcross_go__In.
  assumption.

 destruct (IHxs i j); try assumption.
  left. apply in_or_app. right. assumption.
  right. apply in_or_app. right. assumption.
Qed.