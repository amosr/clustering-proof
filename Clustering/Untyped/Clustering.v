Require Import Clustering.ILP.
Require Import Clustering.List.List.
Require Import Clustering.Tactics.
Require Import Clustering.Untyped.Untyped.

Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.


Section Untyped.


 (* This seems very silly and repetitive *)
 Variable V : Type.

 Hypothesis V_eq_dec
  : forall (a b : V),
    {a = b} + {a <> b}.

 Ltac crunch_eq_decs := crunch_destruct V_eq_dec.

 Variable E : (V * V) -> option EdgeType.
 Variable Vs : list V.
 Definition Pairs := Pairs Vs.

 Hypothesis VsTS : TopSort E Vs.


 Definition NoPreventingEdges (vs : list V) :=
  Forall (fun p => E p <> Some Nonfusible) (cross vs vs).

 Definition NoEdges (yss : list (list V)) (xs : list V) :=
  Forall (fun ys =>
    Forall (fun y =>
      Forall (fun x =>
        E (y,x) = None
      ) xs
    ) ys) yss.

 Inductive Clustering : list (list V) -> Prop :=
 | CNil  : Clustering []
 | CCons vs vss :
           NoPreventingEdges vs ->
           NoEdges vss vs       ->
           Clustering vss       ->
           Clustering (vs::vss).

 Definition singles (vs : list V) : list (list V) :=
  map (fun v => [v]) vs.

 Lemma In_singles x xs:
   In x xs <-> In [x] (singles xs).
 Proof.
  split; intros; induction xs; simpl; inverts~ H; inverts~ H0.
 Qed.

 Lemma In_singles' x xs:
   In x (singles xs) -> exists y, x = [y].
 Proof.
  intros; induction xs.
  inverts H.
  destruct H; eauto.
 Qed.

 Lemma topsort_is_clustering:
  Clustering (map (fun v => [v]) Vs).
 Proof.
  induction~ Vs.
   constructor.
  inverts VsTS.
  constructor~.
  eauto.
  unfold NoPreventingEdges. simpl.
  assert (E (a,a) = None).
   rewrite Forall_forall in H1.
   apply H1. simpl. auto.
   constructor~. rewrite H. intros Hz. inverts Hz.
  simpl in *.
  
  apply IHl in H2.
  inverts H2.
  assert (l = []). destruct l; inverts H0; auto.
  subst. unfold NoEdges. eauto.

  destruct l; inversion H.
  subst.

  inverts H1.
  inverts H7.

  unfold NoEdges in *.

  repeat (rewrite Forall_forall in *; intros).
  destruct H7; try contradiction.
  subst.
  simpl in H1.
  destruct H1.
  subst. inverts H2; try contradiction. auto.


  
  apply H8.
  assert (exists y, x = [y]).
  eapply In_singles'. eassumption.
  destruct H7. subst.
  inverts H2; try contradiction.
  apply In_singles. assumption.
 Qed.

 Hypothesis All_Vs: forall v, In v Vs.
 (* Nodes cannot be mentioned twice *)
 Hypothesis Vs_Unique : Unique Vs.

 Definition Min := MinimalExists (Objective Vs) (Sat_Valid V_eq_dec VsTS All_Vs Vs_Unique).


 Inductive Clustering_Ass (Ass : Assignment (Var V)) : list (list V) -> Prop :=
 | CANil  : Clustering_Ass Ass []
 | CACons vs vss :
           Forall (fun p => Ass (SameCluster p) = 0) (selfcross vs) ->
           Forall (fun vs' => Forall (fun p => Ass (SameCluster p) = 1) (cross vs vs')) vss ->
           Clustering_Ass Ass vss       ->
           Clustering_Ass Ass (vs::vss).

 Definition Clustering_Full (vss : list (list V)) :=
  forall v, In v Vs -> exists vs, In v vs /\ In vs vss.
 
 Definition Ass := assignmentOfMinimal Min.

 Lemma NoPreventingEdges_sgl v:
   NoPreventingEdges [v].
 Proof.
  unfold NoPreventingEdges.
  rewrite Forall_forall.
  intros.
  simpl in *.
  destruct H; try contradiction.
  inverts H.
  assert (In v Vs) by auto.
  clear All_Vs.
  
  induction~ Vs.
  inverts VsTS.
  inverts H3.
  inverts H.
  congruence.
  
  apply~ IHl.
  inverts~ Vs_Unique.
 Qed.

 Lemma NoEdges_sgl vs:
   NoEdges vs [].
 Proof.
  unfold NoEdges.
  repeat (rewrite Forall_forall; intros).
  bye_in_empty.
 Qed.
 
 Lemma Forall_In_not {X} (P : X -> Prop) x xs:
  In x xs ->
  ~ P x ->
  ~ Forall P xs.
 Proof.
  unfold not. intros.
  rewrite Forall_forall in *.
  eauto.
 Qed.

 Lemma Forall_cons_not {X} (P : X -> Prop) x xs:
  ~ Forall P xs ->
  ~ Forall P (x::xs).
 Proof.
  unfold not. intros.
  rewrite Forall_forall in *.
  apply H. intros. apply H0. simpl. eauto.
 Qed.

 Lemma Forall_dec {X} (P : X -> Prop) xs:
   (forall x, {P x} + {~ P x}) ->
   {Forall P xs} + {~ Forall P xs}.
 Proof.
  intros.
  induction~ xs.
  destruct~ IHxs.
  destruct~ (X0 a).
  right. apply (Forall_In_not a); simpl; auto.
  right. apply Forall_cons_not. auto.
 Qed.
 
 Lemma NoEdges_dec vs vss:
   {NoEdges vss vs} + {~ NoEdges vss vs}.
 Proof.
  repeat (apply Forall_dec; intros).
  destruct (E (x0, x1)); eauto.
  right. congruence.
 Qed.

 Lemma NoPreventingEdges_dec vs:
   {NoPreventingEdges vs} + {~ NoPreventingEdges vs}.
 Proof.
  repeat (apply Forall_dec; intros).
  destruct~ (E x); try destruct~ e; left; congruence.
 Qed.
  
  

 Lemma Clustering_insert v xss:
   Clustering xss ->
   (exists ls rs,   ls ++        rs = xss /\ Clustering (ls ++ [[v]]  ++ rs)) \/
   (exists ls m rs, ls ++ [m] ++ rs = xss /\ Clustering (ls ++ [v::m] ++ rs)).
 Proof.
  intros.
  induction H.
  left. repeat exists ([] : list (list V)).
  split. eauto.
  simpl. constructor.
  apply NoPreventingEdges_sgl.
  unfold NoEdges.
  repeat (rewrite Forall_forall; intros).
  bye_in_empty.
  constructor.

  destruct (NoPreventingEdges_dec (v::vs));
  destruct (NoEdges_dec (v::vs) vss).
  right.
  exists ([] : list (list V)) vs vss.
   simpl. split. eauto.
   constructor~.

  destruct IHClustering as [Hc|Hc];
  repeat (destruct Hc as [?x Hc]).
  
  left.
   exists (vs :: x) x0.
   split. simpl. subst. eauto.
   simpl. constructor; eauto.
    simpl. subst.
  Admitted.

 Lemma Clustering_exists Ass:
  Ass = assignmentOfMinimal Min ->
  exists (xss : list (list V)), Clustering xss /\ Clustering_Ass Ass xss /\ Clustering_Full xss.
 Proof.
  intros.
  unfold Min in *.
  unfold Clustering_Full in *.
  induction Vs.
  exists ([] : list (list V)); repeat split; try constructor.
  intros. inverts H0.
 Admitted.

End Untyped.

(*
 Lemma Clustering_exists {V} (Es : V * V -> option EdgeType) VsTS All All_Unique b:
  exists (xss : list (list V)), Clustering Es xss /\ Clustering_Ass b VsTS All All_Unique xss /\ Clustering_Full xss.
 Proof.
  induction Vs.
  simpl.
  induction Vs_Unique.
 Qed.

 Definition insert_same (vv : V * V) (mapz : list (list V)) : list (list V) :=
  match vv with
  | (x,y) => (fix go zs acc : list (list V) :=
              match zs with
              | [] => [acc]
              | (z::zs') =>
                      match (Contains (beqV x) z, Contains (beqV y) z) with
                      | (true , true ) =>      go zs' (acc ++ z)
                      | (false, true ) =>      go zs' (acc ++ z)
                      | (true , false) =>      go zs' (acc ++ z)
                      | (false, false) => z :: go zs'  acc
                      end
              end) mapz [x;y]
  end.

 Definition insert_diff (v : V) (mapz : list (list V)) : list (list V) :=
  (fix go zs : list (list V) :=
              match zs with
              | [] => [[v]]
              | (z::zs') =>
                      match (Contains (beqV v) z) with
                      | true  =>      z :: zs'
                      | false =>      z :: go zs'
                      end
              end) mapz.


 Definition Clustering (a : Assignment Var) : list (list V)
  := let munge mapz vv :=
          match a (SameCluster vv) with
          | 0 => insert_same   vv mapz
          | _ => match vv with
                 | (x,y) => insert_diff x
                          ( insert_diff y mapz )
                 end
          end
     in  fold_left munge Pairs [].

 End Untyped.
*)
(*

 Inductive Clustering (a : Assignment Var) : list V -> Prop
  := Cl_Nil  : Clustering a []
   | Cl_Cons bs vs : Clustering a vs
     -> (Forall (fun v => a (SameCluster v) = 0) (selfcross bs))
     -> (Forall (fun v => a (SameCluster v) = 1) (cross bs vs))
     -> (Forall (fun b => ~ In b vs) bs)
     -> Clustering a (bs++vs).


 Lemma Clustering_insert (a : Assignment Var) xs ins
    : Valid Constraints a
   -> Clustering a xs
   -> exists pre post,
   Clustering a (pre ++ [ins] ++ post) /\ pre ++ post = xs.
 Proof.
  intros.
  induction H0.
   exists []. exists [].
    split; repeat constructor; eauto.

  destruct IHClustering.
  destruct H4.
  destruct H4.

  induction Vs.
   exists [].
    repeat split; eauto; constructor.

 Lemma valid_assignment_is_Clustering (a : Assignment Var)
    : Valid Constraints a
   -> exists verts,
   Clustering a verts /\ (forall x, In x verts <-> In x Vs) /\ length verts = length Vs.
 Proof.
  intros.
  induction Vs.
   exists [].
    repeat split; eauto; constructor.
 destruct Vs; subst; eauto; inversion HeqLen.
    split. constructor. split. split; eauto. eauto.

   
   
  intros.
  destruct H.
 Admitted.

*)




(*

 Lemma Clustering_SC : forall Vs a,
       Valid (Constraints Vs) a ->
       forall cs,
       In cs (Clustering Vs a) ->
       forall c d,
       In c cs /\ In d cs <->
       a (SameCluster (c, d)) = 0.
 Proof.
  intros Vs.
   induction Vs as [| v vs]; intros.
   simpl in *. inversion H0.

   remember (Constraints Vs) as Cons.
   induction H.
   
  intros.
   destruct Vs.
   simpl in *.
   destruct H.
   destruct Vs.
   simpl in *.
   destruct H.

   simpl in *.

    unfold Constraints in *.
    unfold Pairs in *.
    simpl in *.
     destruct (E (v, v0)); try destruct e; inversion HeqCons.

  intros.
   

   unfold Constraints.
   admit.

   simpl in *.
   inversion H0.

   inversion H.
   unfold Constraints in H2.
   unfold Pairs in H2.
   simpl in H2.
   inversion H2.
   eauto.
   unfold Constraints in *.
   inversion H.

 Lemma Clustering_SC : forall (a : Assignment Var) i j,
       Valid Constraints a ->
       forall c,
       In c (Clustering a) ->
       In a c /\ In a c <->
       a (SameCluster (i, j)) = 0.
 Admitted.

 Lemma Clustering_Pi : forall (a : Assignment Var) i j,
       Valid Constraints a ->
       a (Pi i) > a (Pi j) ->
       Clustering a i > Clustering a j.
 Admitted.


 Definition Sat : Assignment Var.
 Admitted.

 Lemma valid : Valid Constraints Sat.
 Admitted.
*)

