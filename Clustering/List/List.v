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



  Lemma selfcross_go_Once: forall {V} i j (l : list V),
    ~In i l -> In j l ->
    In (i,j) (selfcross_go i l).
  Proof.
   intros.
   induction l; eauto.
   simpl.
   inverts H0.
    left~.
    right. apply IHl.
   unfold not in *.
    intros.
   apply H. apply in_cons. assumption.
   assumption.
  Qed.

  Lemma selfcross_go_Not: forall {V} a i j (l : list V),
    a <> i ->
    ~ In (i,j) (selfcross_go a l).
  Proof.
   intros.
   unfold not. intros.
   induction l; eauto.
   simpl in *.
   apply IHl.
   inverts H0. inverts H1. destruct H. reflexivity.
   assumption.
  Qed.

  Lemma selfcross_Not: forall {V} i j (l : list V),
    ~In i l ->
    ~In (i,j) (selfcross l).
  Proof.
   intros.

   unfold not in *.
   intros.
   apply H.

   induction l; eauto.
   
   simpl in *.
   
   apply in_app_or in H0.
   destruct H0.
   
   apply selfcross_go_Not in H0. destruct H0.
   unfold not. intros. apply H. left. assumption.

   right. apply IHl.
    intros. apply H. right. assumption.
    assumption.
  Qed.


Inductive Unique {A} : list A -> Prop :=
 | Unique_nil : Unique []
 | Unique_cons x xs : ~ In x xs -> Unique xs -> Unique (x::xs).



Lemma not_In__not_In_selfcross_go {A} (i j k: A) xs:
  ~ In j xs ->
  ~ In (i,j) (selfcross_go k xs).
Proof.
 unfold not.
 intros.
 induction~ xs.
 simpl in *.
 destruct H0.
  inverts H0.
 apply H; eauto.
 apply IHxs. intros. apply H. right. assumption.
 assumption.
Qed.

Lemma not_In__not_In_selfcross {A} (i j : A) xs:
  ~ In j xs ->
  ~ In (i,j) (selfcross xs).
Proof.
 unfold not.
 intros.
 induction~ xs.
 simpl in *.
 apply in_app_or in H0.
 destruct H0.
 eapply not_In__not_In_selfcross_go; eauto.
 apply IHxs; eauto.
Qed.

Lemma In_selfcross_go__In2 {A} i j k (xs : list A):
   In (i,j) (selfcross_go k xs) ->
   In j xs.
Proof.
 intros.
 induction~ xs.
  destruct H.
   left. inverts~ H.
   right. auto.
Qed.

Lemma In_selfcross__In2 {A} i j (xs : list A):
   In (i,j) (selfcross xs) ->
   In j xs.
Proof.
 intros.
 induction~ xs.
 simpl in H.
 apply in_app_or in H.
 destruct H.
 simpl. right.
 eapply In_selfcross_go__In2. eassumption.
 
 simpl. right. auto.
Qed.


Lemma In_selfcross_go__fst {A} (i j x : A) xs:
  In (i,j) (selfcross_go x xs) ->
  i = x.
Proof.
 intros.
 induction~ xs.
  inverts H.
 simpl in *.
  inverts H.
 inverts H0. auto.
 apply IHxs. auto.
Qed.

Lemma In_selfcross_go__not_In {A} (x : A) x0 xs:
  ~ In x xs ->
  In x0 (selfcross_go x xs) ->
  ~ In x0 (selfcross xs).
Proof.
 unfold not. intros.
 induction~ xs.
 simpl in *.
 apply in_app_or in H1.

 destruct x0.
 assert (a0 = x).
  destruct H0. inverts H0. auto.
  eapply In_selfcross_go__fst; eassumption.
 subst.

 destruct H1.
  assert (x = a).
   eapply In_selfcross_go__fst; eassumption.
  auto.

 apply IHxs; auto.
 
 destruct H0; auto.
 inverts H0.
 
 apply selfcross_go__In.

 eapply In_selfcross__In2. eassumption.
Qed.


Lemma unique__not_in_selfcross {A} (i : A) j xs rest:
 Unique xs ->
 selfcross xs = (i,j) :: rest ->
 ~ In (i,j) rest.
Proof.
 intros.
 destruct xs. inverts H0.
 destruct xs. inverts H0.
 simpl in H0.
 assert (a = i /\ a0 = j) by inverts~ H0.
 destruct H1.
 subst.
 inverts H.
 inverts H4.
 inverts H0.

 unfold not in *.
 intros.
 apply in_app_or in H.
 destruct H.

 apply not_In__not_In_selfcross_go in H; assumption.

 apply in_app_or in H.
 destruct H.

 assert (i <> j). simpl in H3. auto.
 apply selfcross_go_Not in H; auto.
 apply not_In__not_In_selfcross in H; eauto.
Qed.


Lemma unique_selfcross_go {A} i (xs : list A):
 Unique (i::xs) ->
 Unique (selfcross_go i xs).
Proof.
 intros.
 induction xs.
  constructor.
 simpl in *.
 inverts H.
 inverts H3.
 assert (~ In i xs). simpl in *. auto.
 constructor.
  apply not_In__not_In_selfcross_go. assumption.
 apply IHxs.
  constructor; assumption.
Qed.

Lemma unique_app {A} (xs ys : list A):
 Unique xs -> Unique ys ->
 Forall (fun x => ~ In x ys) xs ->
 Unique (xs++ys).
Proof.
 induction~ xs; intros.
 simpl.
 inverts H.
 inverts H1.
 constructor.
  unfold not in *.
  intros.
  apply in_app_or in H.
  destruct H; auto.
 auto.
Qed.

Lemma unique_selfcross {A} (xs : list A):
 Unique xs ->
 Unique (selfcross xs).
Proof.
 intros.
 induction H.
  constructor.
 simpl.
 assert (Unique (selfcross_go x xs)).
  apply unique_selfcross_go.
   constructor; assumption.

 apply unique_app; try assumption.
 apply Forall_forall.
 unfold not in *.
 intros.
 
 eapply In_selfcross_go__not_In in H; try eassumption.
 apply H. assumption.
Qed.


Lemma In_not_In__not_eq {A} i j (xs : list A):
   In i xs ->
 ~ In j xs ->
 i <> j.
Proof.
 intros.
 induction~ xs.
 simpl in *.
 inverts~ H.
Qed.

Lemma unique_In__not_eq {A} i j (xs : list A):
 Unique xs ->
 In (i,j) (selfcross xs) ->
 i <> j.
Proof.
 intros HUnique HIn.
 induction HUnique; auto.
 simpl in HIn.
 apply in_app_or in HIn.
 destruct HIn.
 assert (i = x) by (eapply In_selfcross_go__fst; eassumption).
 subst.
 assert (In j xs) by (eapply In_selfcross_go__In2; eassumption).
 assert (j <> x) by (eapply In_not_In__not_eq; eassumption).
 auto.
 auto.
Qed.

Lemma unique_In__not_swap_In {A} i j (xs : list A):
 Unique xs ->
 In (i,j) (selfcross xs) ->
 ~ In (j,i) (selfcross xs).
Proof.
 intros.
 assert (i <> j) by (eapply unique_In__not_eq; eassumption).
 induction~ H.
 simpl in *.
 apply in_app_or in H0.
 destruct H0.
 assert (i = x) by (eapply In_selfcross_go__fst; eassumption).
 subst.
 unfold not; intros HIn.
 apply in_app_or in HIn.
 destruct HIn.
  assert (j = x) by (eapply In_selfcross_go__fst; eassumption).
   auto.
  apply H.
  eapply In_selfcross__In2; eassumption.
 unfold not; intros HIn.
 apply in_app_or in HIn.
 destruct HIn.
  assert (j = x) by (eapply In_selfcross_go__fst; eassumption).
  subst.
  assert (In x xs) by (eapply In_selfcross__In2; eassumption).
  auto.
 apply IHUnique; assumption.
Qed.

