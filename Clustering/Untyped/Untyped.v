(* Simplification of Megiddo's ILP clustering algorithm:
   one type, and no weights.
*)

Require Import Clustering.ILP.
Require Import Clustering.List.List.
Require Import Clustering.List.Index.
Require Import Clustering.Tactics.

Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

Section Untyped.
 (* The first step is to define the graph that we are working on.
    This is a simple graph, with fusible and fusion-preventing edges.
    There is only a single node type -- that is, all nodes may
    be fused together if edges permit.
    This is equivalent to the loops all having the same loop bounds.
 *)

 (* Type of nodes *)
 Variable V : Type.

 (* Need to be able to test if two nodes are equal *)
 Hypothesis V_eq_dec
  : forall (a b : V),
    {a = b} + {a <> b}.

 (* This is a helper tactic to find all node equality tests in the goal,
    and perform case analysis over them. All of them. *)
 Ltac crunch_eq_decs := crunch_destruct V_eq_dec.


 (* Edges may be fusible or non *)
 Inductive EdgeType : Type
  := Fusible
   | Nonfusible.

 (* Is there an edge between two? If so, what kind *)
 Variable E : (V * V) -> option EdgeType.

 (* We need a list of all the nodes *)
 Variable Vs : list V.

 (* A topological ordering of nodes:
    if P is before Q, there are no edges from Q to P
    (but there may be edges from P to Q)
 *)
 Inductive TopSort : list V -> Prop
   := TS_Nil  : TopSort nil
    | TS_Cons : forall x xs,
                Forall (fun y => E (y, x) = None) (x::xs) ->
                TopSort xs ->
                TopSort (x::xs).

 (* Our list must be a topological ordering *)
 Hypothesis VsTS : TopSort Vs.
 (* The list must also be complete - all nodes are mentioned *)
 Hypothesis All_Vs: forall v, In v Vs.
 (* Nodes cannot be mentioned twice *)
 Hypothesis Vs_Unique : Unique Vs.

 (* Because of the topological sort, we know that if there is
    an edge between two nodes P and Q, Q must be strictly after P.
    I think this proof could be cleaned up a lot.
    
    The index_of preconditions are also unnecessary, but require:
    Lemma All_Vs_Index i :
      exists ixi, index_of V_eq_dec i Vs = Some ixi *)      
 Lemma Edge__TS_index_gt i j et ixI ixJ:
       E (i,j) = Some et ->
       index_of V_eq_dec i Vs = Some ixI ->
       index_of V_eq_dec j Vs = Some ixJ ->
       (ixI < ixJ)%nat.
 Proof.
  intros HE Hi Hj.
   assert (In i Vs) by auto.
   assert (In j Vs) by auto.
  clear All_Vs Vs_Unique.
  gen ixI ixJ.
  induction Vs; intros. inverts Hi. inverts VsTS. simpl in *.
  destruct (V_eq_dec i a). subst. inverts Hi. destruct (V_eq_dec j a).
   assert (Some et = None).
    inverts H3. subst. rewrite <- H5. rewrite <- HE. auto.
   inverts H1.
   inverts H0. destruct~ n.
    apply (In__index_of V_eq_dec) in H1.
    destruct H1.
    rewrite H0 in Hj.
    inverts Hj. omega.

 destruct  H; destruct  H0; subst.
 destruct~ n. destruct~ n.

 assert (E (i,j) = None) as HENone.
 inverts H3.
 eapply Forall_forall in H5; eassumption.

 rewrite HENone in HE. inverts HE.

 remember H  as HInI.
 remember H0 as HInJ.
 clear HeqHInI. clear HeqHInJ.
 apply (In__index_of V_eq_dec) in H.  destruct H.
 apply (In__index_of V_eq_dec) in H0. destruct H0.

 rewrite H  in Hi. rewrite H0 in Hj.
 destruct (V_eq_dec j a). subst.
 assert (E (i,a) = None) as HENone.
  inverts H3.
  eapply Forall_forall in H6;
  eassumption.
 rewrite HENone in HE.
 inverts HE.

 inverts Hi.
 inverts Hj.

 assert (x < x0)%nat.
 eapply IHl; try eassumption.
 omega.
 Qed.

 Lemma NoSelfEdges i:
  E (i,i) = None.
 Proof.
  assert (In i Vs) as InI by auto.
  clear All_Vs.
  induction Vs. inverts InI.
  inverts VsTS.
  inverts Vs_Unique.
  destruct InI.
  subst.
  eapply Forall_forall in H1; simpl; eauto.
  apply~ IHl.
 Qed.
  

  (* With Vs and E defined, we now have a graph that we can cluster.
     We define the ILP variables, the constraints, and the
     objective function.
  *)

  (* The type of ILP variables.
      SameCluster(i,j) = 0 iff i and j are clustered together
      Pi(i) is used to encode precedence and acyclic constraints:
       if there is a non-fusible edge between i and j, then
        Pi(i) < Pi(j).
       if SameCluster(i,j) = 0, then Pi(i) = Pi(j)

     Actually, Pi needn't be integral, which makes the
     ILP solver's job easier.
  *)
  Inductive Var : Type
   := SameCluster : (V * V) -> Var
    | Pi          :      V  -> Var.

  (* Cross product of nodes, irreflexive and asymmetric.
     This is a slight simplification that lets us use around
     N*(N/2) SameCluster variables, instead of N*N.
  *)
  Definition Pairs : list (V * V)
   := selfcross Vs.

  (* Since every i,j are in Vs, (i,j) must be in cross product of Vs.
     However, since it is asymmetric, one of (i,j) or (j,i) will be in.
  *)
  Lemma All_Pairs: forall i j,
      i <> j ->
      In (i,j) Pairs \/ In (j,i) Pairs.
  Proof.
   unfold Pairs. intros.
   apply selfcross__In; try assumption; apply All_Vs.
  Qed.

  (* And since it is irreflexive, any two nodes in Pairs are not equal
  *)
  Lemma In_Pairs__ne: forall i j,
      In (i,j) Pairs ->
      i <> j.
  Proof.
   unfold Pairs. intros.
   eapply unique_In__not_eq; eauto.
  Qed.


  Lemma Pairs_Unique:
   Unique Pairs.
  Proof.
   apply unique_selfcross. assumption.
  Qed.



 (* N is the number of nodes.
    This is used as a number big enough to be effectively unconstrained.
    For example, the constraint
      -N < Pi(i) < N
    gives more than enough room for all Pi(i) (there are only N)
    to not be the same.
 *)
  Definition N : Z
   := Z_of_nat (length Vs).


 (* The objective function is simply to minimise all clusters with
    equal weight *)
 (* Maybe extract definition of clusters so it's easier to talk about
    objectives of specific pairs *)
 Definition Objectives (ps : list (V * V)) : Linear Var
  := let clusters
          := map (fun p => var1 (SameCluster p)) ps
     in  fold_right (fun x y => x |+| y) (const _ 0) clusters.

 Definition Objective : Linear Var
  := Objectives Pairs.


 (* Define constraint for a pair of nodes *)
 (* TODO: extract the selfs here into separate definition, see below *)
 Definition ConstraintOfPair (vv : V * V) : list (C Var)
  := let Sc     := SameCluster vv in
     let ScR    := match vv with
                   | (i,j) => SameCluster (j,i)
                   end in
     (* SameCluster is symmetric *)
     let ScReq  := var1 Sc |==| var1 ScR in
     (* SameCluster is boolean - 0 or 1 *)
     let Bounds := const _ 0 |<=| var1 Sc |<=| const _ 1 in
     (* This shouldn't exactly be here, but:
        clustering is reflexive. SameCluster(i,i) is always 0. *)
     let Selfs  := match vv with
                   | (i,j) => constrs
                     [ var1 (SameCluster (i,i)) |==| const _ 0
                     ; var1 (SameCluster (j,j)) |==| const _ 0 ]
                   end in
     (* Look up whether there is an edge between these two nodes *)
     match (vv, E vv) with
       (* No edge *)
         | ((i,j), None)
           (* If SameCluster i j, then Pi i = Pi j
              Otherwise Pis are unconstrained *)
           => constrs
            [ var (-N) Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds
            ; ScReq
            ; Selfs ]
       (* A fusible edge *)
         | ((i,j), Some Fusible)
           (* If SameCluster i j, then Pi i = Pi j
              Otherwise Pi i < Pi j *)
           => constrs
            [ var1     Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds
            ; ScReq
            ; Selfs ]
       (* A non-fusible edge *)
         | ((i,j), Some Nonfusible)
           (* SameCluster i j = 1, and Pi i < Pi j *)
           => constrs
            [ var1 (Pi i) |<| var1 (Pi j)
            ; var1 Sc |==| const _ 1
            ; ScReq
            ; Selfs]
         end.

 (* Cont'd TODO: extract the selfs out of ConstraintOfPair, so we have

    constrs (map ConstraintOfPair Pairs) ++
    constrs (map SelfConstraint   Vs)
   where SelfConstraint i = SameCluster(i,i) |==| 0
   
    The current definition has superfluous selfs, *and* only has selfs
    if there's more than one node in Vs.
    This wouldn't be much of a problem in practice, but it makes the
    proofs messier (see V__Sc_refl)
   *)
 Definition Constraints : list (C Var)
  := constrs (map ConstraintOfPair Pairs).

 (* The minimality axiom requires that there exists at least
    one valid assignment. For simplicity, we just create the
    assignment for the clustering with no fusion at all. *)
 Definition Sat := fun x =>
  match x with
  (* a pair of nodes not in same cluster *)
  | SameCluster (i,j)
  => if   V_eq_dec i j
     then 0
     else 1
  (* pi is index in topological sort *)
  | Pi i
  => match index_of V_eq_dec i Vs with
     | Some n => Z_of_nat n
     | None   => 0
     end
  end.

 (* Prove that the assignment is valid. *)
 Lemma Sat_Valid: Valid Constraints Sat.
 Proof.
  unfold Constraints.
  induction Pairs;
  validate; simpl.
  apply Valid_app_and.
  split~.
  unfold ConstraintOfPair.
  remember (E a) as Edge.
  destruct a as [i j].

   assert (exists ixi, index_of V_eq_dec i Vs = Some ixi) as IndexI.
    apply In__index_of.
    apply All_Vs.
   assert (exists ixj, index_of V_eq_dec j Vs = Some ixj) as IndexJ.
    apply In__index_of.
    apply All_Vs.
   destruct IndexI as [ixi Hixi]; destruct IndexJ as [ixj Hixj].

   assert (ixi < length Vs)%nat.
    eapply index_of__lt_length. eassumption.
   assert (ixj < length Vs)%nat.
    eapply index_of__lt_length. eassumption.


 assert (Z_of_nat ixi < N).
  unfold N. omega.
 assert (Z_of_nat ixj < N).
  unfold N. omega.
 assert (Z_of_nat ixi >= 0).
  omega.
 assert (Z_of_nat ixj >= 0).
  omega.

  destruct Edge as [e|]; try destruct e;
    validate;
     Z_simp_all; try omega;
     crunch_eq_decs;
     try solve [subst; rewrite NoSelfEdges in HeqEdge; inverts HeqEdge];
     try solve [destruct~ n];
     Z_simp_all; try omega;
    try rewrite Hixi;
    try rewrite Hixj;
  try assert (ixi < ixj)%nat by (eapply Edge__TS_index_gt; eauto);
  try unfold N in *;
  try destruct (Z.of_nat (length Vs));
  try assert (ixi = ixj) by congruence;
  simpl;
  try omega.

 assert (Z.neg p = - Z.pos p).
  simpl. reflexivity.
 simpl. rewrite H5. omega.

 assert (Z.neg p = - Z.pos p).
  auto.
 simpl.
 rewrite H5 in *.
 omega.
 Qed.

 (* Now we know that there's at least one assignment that
    minimises Objective *)
 Definition Min := MinimalExists Objective Sat_Valid.


 (* Find any "Valid (ConstraintOfPair ij)" in hypotheses.
    Perform case analysis on different types of edges,
    and crunch each list of constraints into actual
    value constraints usable by omega *)
 Ltac crunch_valid_edge :=
  match goal with
   | [ H : Valid (ConstraintOfPair ?a) _ |- _]
   => unfold ConstraintOfPair in H;
      let i := fresh "i" in
      let j := fresh "j" in
      let e := fresh "e" in
      destruct a as [i j];
      destruct (E (i,j)) as [e|];
      try destruct e;
      crunch_valid H
  end.


 Lemma V__Sc_Bool (a : Assignment Var) i j :
   i <> j ->
   Valid Constraints a ->
   a (SameCluster (i,j)) = 0 \/ a (SameCluster (i,j)) = 1.
 Proof.
  intros HNe HVal.
   unfold Constraints in *.

   apply All_Pairs in HNe.
   induction Pairs.
    inversion HNe; inversion H.
   simpl in *.

   apply Valid_app_and in HVal.
   destruct HVal as [HVij HVrest].

   inverts HNe; inverts H;
     try (apply IHl; try left; assumption);
     try (apply IHl; try right; assumption);
     try (crunch_valid_edge; omega).
 Qed.

 Lemma V__Sc_refl (a : Assignment Var) i j :
   (* this is a surprising requirement *)
   (* it turns out that if |Vs| == 1, then there *are* no constraints, *)
   (* so Sc(i,i) may in fact not be 0 *)
   i <> j              ->
   Valid Constraints a ->
   a (SameCluster (i,i)) = 0.
 Proof.
  intros.
  unfold Constraints in *.
  
  assert (In (i,j) Pairs \/ In (j,i) Pairs) as InIJ by apply~ All_Pairs.
  induction Pairs.
   destruct InIJ as [II|II]; inverts II.
  
  simpl in *.
  apply Valid_app_and in H0.
  destruct H0.
  destruct InIJ as [II|II]; destruct II; subst;
   try solve [crunch_valid_edge; omega];
   try solve [apply~ IHl].
 Qed.

 Lemma V__Sc_sym (a : Assignment Var) i j :
   i <> j ->
   Valid Constraints a ->
   a (SameCluster (i,j)) = a (SameCluster (j,i)).
 Proof.
  intros HNe HVal.
   unfold Constraints in *.
   apply All_Pairs in HNe.

   induction Pairs.
    inverts HNe; inverts H.
   simpl in *.

   apply Valid_app_and in HVal.
   destruct HVal as [HVij HVrest].

   inverts HNe; inverts H;
     try (apply IHl; try left; assumption);
     try (apply IHl; try right; assumption);
     try (crunch_valid_edge; omega).
 Qed.


 Lemma V_Sc__Pi (a : Assignment Var) i j :
   Valid Constraints a ->
   In (i,j) Pairs      ->
   a (SameCluster (i,j)) = 0 ->
   a (Pi i) = a (Pi j).
 Proof.
  intros HVal HIn HSame.
  unfold Constraints in *.

  induction Pairs.
   inversion HIn.

  simpl in *.
  apply Valid_app_and in HVal.
  destruct HVal as [HVij HVrest].
  destruct HIn; try (apply IHl; assumption).
  subst.
  crunch_valid_edge; rewrite HSame in *; omega.
 Qed.

 Definition update_Sc (a_orig : Assignment Var) i j new_value : Assignment Var :=
  (fun x =>
   match x with
   | SameCluster (a,b)
   => if   Sumbool.sumbool_and _ _ _ _ (V_eq_dec a i) (V_eq_dec b j)
      then new_value
      else if   Sumbool.sumbool_and _ _ _ _ (V_eq_dec a j) (V_eq_dec b i)
      then new_value
      else a_orig x
   | _ => a_orig x end).

 Lemma update_Sc_Valid1 a i j v p:
  Valid (ConstraintOfPair p) a ->
  (i,j) <> p -> (j,i) <> p ->
  i <> j ->
  Valid (ConstraintOfPair p) (update_Sc a i j v).
 Proof.
  intros.
   unfold ConstraintOfPair.
   unfold update_Sc.
   crunch_valid_edge;
   
   validate; simpl;
   crunch_eq_decs; simpl;
   
   try solve [subst; contradiction];
   try solve [destruct H0; subst; auto];
   try solve [destruct H1; subst; auto];
   try omega.
 Qed.

 Lemma update_Sc_Valid a i j v ps:
  Valid (constrs (map ConstraintOfPair ps)) a ->
  ~ In (i,j) ps -> ~ In (j,i) ps ->
  i <> j ->
  Valid (constrs (map ConstraintOfPair ps)) (update_Sc a i j v).
 Proof.
  intros.
  induction ps.
   constructor.
  simpl in *.
  apply Valid_app_and.
  apply Valid_app_and in H.
  destruct H.

  split.
   apply update_Sc_Valid1; auto.

  apply IHps; auto.
 Qed.

 Lemma update_Sc_Obj_not_in a i j v ps:
   ~ In (i,j) ps ->
   ~ In (j,i) ps ->
   obj (Objectives ps) (update_Sc a i j v) =
   obj (Objectives ps) a.
 Proof.
  intros.
  unfold Objectives. unfold obj.
  induction ps; auto.
  
  simpl.
  repeat rewrite value_app_plus.
  simpl in *.
  rewrite IHps; auto.
  simpl.
  destruct a0.
  crunch_eq_decs; simpl; subst;
   try solve [destruct n; auto];
   try solve [destruct H; left; auto];
   try solve [destruct H0; left; auto];
   omega.
 Qed.

 Lemma update_Sc_Obj' a i j v ps:
   Unique ps     ->
     In (i,j) ps ->
   ~ In (j,i) ps ->
   obj (Objectives ps) (update_Sc a i j v) =
   obj (Objectives ps) a + v - a (SameCluster (i,j)).
 Proof.
  intros HUn HIn HNIn.
  induction HUn.
   inverts HIn.
  simpl in *.
  destruct HIn.
   subst.
   assert (obj (Objectives xs) (update_Sc a i j v) = obj (Objectives xs) a)
    by (apply update_Sc_Obj_not_in; auto).
   unfold Objectives in *.
   simpl in *.
   unfold obj in *.
   simpl.
   repeat rewrite value_app_plus in *.
   rewrite H0.
   simpl.
   crunch_eq_decs; bye_not_eq; simpl; omega.

 unfold Objectives in *.
 unfold obj in *.
 simpl in *.
 repeat rewrite value_app_plus in *.
 rewrite IHHUn; auto.
 simpl.
 destruct x as [k l].
 
 crunch_eq_decs; simpl; substs;
   try solve [destruct n; auto];
   try solve [destruct H; auto];
   try solve [destruct H0; auto];
   try solve [destruct HNIn; auto];
   try solve [omega].
 Qed.

 Lemma update_Sc_Obj a i j v:
   In (i,j) Pairs ->
   obj Objective (update_Sc a i j v) =
   obj Objective a + v - a (SameCluster (i,j)).
 Proof.
  unfold Objective.
  intros.
  rewrite update_Sc_Obj'; auto.
  apply Pairs_Unique.

  unfold Pairs in *.
  apply unique_In__not_swap_In; auto.
 Qed.


 Lemma V_Pi_Min__Sc (a : Assignment Var) i j:
   In (i,j) Pairs ->
   i <> j ->
   Valid Constraints a ->
   a (Pi i) = a (Pi j)      ->
   a = assignmentOfMinimal Min ->
   a (SameCluster (i,j)) = 0.
 Proof.
  intros HIn HEq HVal HPi HMin.
  destruct Min; simpl in *; subst.

  remember (update_Sc a0 i j 0 : Assignment Var) as b.


  assert (a0 (SameCluster (i,j)) = 0 \/ a0 (SameCluster (i,j)) = 1) as HSc01.
   eapply V__Sc_Bool; assumption.
  assert (a0 (SameCluster (i,j)) = a0 (SameCluster (j,i))) as HScRefl.
   eapply V__Sc_sym; assumption.
  assert (a0 (SameCluster (i,i)) = 0) as HScII0.
   eapply V__Sc_refl; eassumption.
  assert (a0 (SameCluster (j,j)) = 0) as HScJJ0.
   eapply V__Sc_refl; eauto.

  clear All_Vs v.
  assert (Unique Pairs) as HUnique. apply unique_selfcross. assumption.
  assert (~ In (j,i) Pairs) as HNotSwap by (
   apply unique_In__not_swap_In; assumption).

  assert (Valid Constraints b) as ValB.
      subst.
      unfold Constraints in *.
      clear l.
      induction Pairs.
       simpl. constructor.
      simpl in *.
      apply Valid_app_and.
      apply Valid_app_and in HVal.
      destruct HIn. subst.
      split.
      unfold update_Sc in *.
       unfold ConstraintOfPair.
       remember (E (i,j)) as Edge.
       destruct Edge; try destruct e; simpl;
           validate; simpl; crunch_eq_decs; simpl;
           bye_not_eq;
           try assert (a0 (Pi i) < a0 (Pi j)) by
              (destruct HVal as [HVA HVB];
               unfold ConstraintOfPair in HVA;
               rewrite <- HeqEdge in HVA;
               crunch_valid HVA;
               omega);
            omega.
     inverts HUnique.
     destruct HVal.
     apply update_Sc_Valid; auto.
   
   destruct HVal as [HVal1 HVal2].
   split.
    assert (a <> (i,j)).
     inverts HUnique.
     unfold not. intros.
     apply H2.
     subst. assumption.
    apply update_Sc_Valid1; auto.
   inverts HUnique.
   apply IHl; auto.

 assert (b (SameCluster (i,j)) = 0).
  rewrite Heqb. simpl.
   crunch_eq_decs; simpl; auto;
     try solve [bye_not_eq].
 rewrite <- H.

 assert (obj Objective a0 <= obj Objective b) by auto.
 assert (obj Objective b = obj Objective a0 + 0 - a0 (SameCluster (i,j))).
  subst.
  applys update_Sc_Obj. assumption.

 omega.
Qed.
  
 Lemma V__Sc_trans (a : Assignment Var) i j k:
   Valid Constraints a         ->
   In (i,k) Pairs              ->
   In (i,j) Pairs              ->
   In (j,k) Pairs              ->
   a = assignmentOfMinimal Min ->
   a (SameCluster (i,j)) = 0   ->
   a (SameCluster (j,k)) = 0   ->
   a (SameCluster (i,k)) = 0.
 Proof.
  intros.
  assert (a (Pi i) = a (Pi j)) by apply~ V_Sc__Pi.
  assert (a (Pi j) = a (Pi k)) by apply~ V_Sc__Pi.
  assert (a (Pi i) = a (Pi k)) by congruence.
  assert (i <> k) by apply~ In_Pairs__ne.
  
  apply~ V_Pi_Min__Sc.
 Qed.


 Lemma V__Sc_trans2 (a : Assignment Var) i j k:
   Valid Constraints a         ->
   a = assignmentOfMinimal Min ->
   a (SameCluster (i,j)) = 0   ->
   a (SameCluster (j,k)) = 0   ->
   a (SameCluster (i,k)) = 0.
 Proof.
  intros.
  destruct (V_eq_dec i j); destruct (V_eq_dec j k);
                           destruct (V_eq_dec i k);
                           try solve [subst; auto].

  asserts_rewrite~ (i = k).
  apply~ V__Sc_refl. eauto.
  
  assert (a (SameCluster (i,j)) = a (SameCluster (j,i))) as Rij by apply~ V__Sc_sym.
  assert (a (SameCluster (j,k)) = a (SameCluster (k,j))) as Rjk by apply~ V__Sc_sym.
  assert (a (SameCluster (i,k)) = a (SameCluster (k,i))) as Rik by apply~ V__Sc_sym.

  assert (In (i,j) Pairs \/ In (j,i) Pairs) as Iij by apply~ All_Pairs.
  assert (In (j,k) Pairs \/ In (k,j) Pairs) as Ijk by apply~ All_Pairs.
  assert (In (i,k) Pairs \/ In (k,i) Pairs) as Iik by apply~ All_Pairs.

  Ltac pi_same a i j :=
   assert (a (Pi i) = a (Pi j)) by (
        try solve [apply~ V_Sc__Pi];
        try solve [symmetry; apply~ V_Sc__Pi; congruence]
      ).

  destruct Iij;
  destruct Ijk;
  destruct Iik;
  pi_same a i j;
  pi_same a j k;
  assert (a (Pi i) = a (Pi k)) by congruence;


  assert (i <> k) by (
    try solve [apply~ In_Pairs__ne];
    try solve [
        assert (k <> i) by apply~ In_Pairs__ne;
        auto
    ]
  );
  try solve [
    apply~ V_Pi_Min__Sc
  ];
  try solve [
    rewrite Rik;
    apply~ V_Pi_Min__Sc
  ].
 Qed.


End Untyped.
