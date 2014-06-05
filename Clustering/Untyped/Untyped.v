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
 
 (* Type of nodes *)
 Variable V : Type.

 (* Equality must be decidable *)
 Hypothesis V_eq_dec
  : forall (a b : V),
    {a = b} + {a <> b}.

 (* Edges may be fusible or non *)
 Inductive EdgeType : Type
  := Fusible
   | Nonfusible.

 (* Is there an edge between two? If so, what kind *)
 Variable E : (V * V) -> option EdgeType.

  (* There must exist a topological ordering *)
  Variable Vs : list V.
 
  Inductive TopSort : list V -> Prop
   := TS_Nil  : TopSort nil
    | TS_Cons : forall x xs,
               Forall (fun y => E (y, x) = None) (x::xs) ->
               ~ In x xs ->
               TopSort xs ->
               TopSort (x::xs).

  Hypothesis VsTS : TopSort Vs.
  Hypothesis All_Vs: forall v, In v Vs.

  Lemma Edge__TS_index_gt: forall i j et ixI ixJ,
        E (i,j) = Some et ->
        In i Vs -> In j Vs ->
        index_of V_eq_dec i Vs = Some ixI ->
        index_of V_eq_dec j Vs = Some ixJ ->
        (ixI < ixJ)%nat.
  Proof.
   intros.
   clear All_Vs.
   gen ixI ixJ.
   induction Vs; intros.
   inversion H0.
   inverts VsTS.
   simpl in *.
   destruct (V_eq_dec i a).
    subst.
    inverts H2.
    destruct (V_eq_dec j a).
    assert (Some et = None).
      inverts H6. subst. rewrite <- H5. rewrite <- H. auto.
     inverts H2.

    inverts H1. destruct~ n.
    apply (In__index_of V_eq_dec) in H2.
    destruct H2.
    rewrite H1 in H3.
    inverts H3. omega.

 destruct H0; destruct H1; subst.
 destruct~ n.
 destruct~ n.

 assert (E (i,j) = None) as HENone.
 inverts H6.
 eapply Forall_forall in H9; eassumption.
 
 rewrite HENone in H.
 inverts H.

 remember H0 as HInI.
 remember H1 as HInJ.
 clear HeqHInI. clear HeqHInJ.
 apply (In__index_of V_eq_dec) in H0.
 destruct H0.
 apply (In__index_of V_eq_dec) in H1.
 destruct H1.

 rewrite H0 in H2.
 rewrite H1 in H3.
 destruct (V_eq_dec j a).

 subst.
 assert (E (i,a) = None) as HENone.
  inverts H6.
  eapply Forall_forall in H10;
  eassumption.
 rewrite HENone in H.
 inverts H.
 
 inverts H2.
 inverts H3.

 assert (x < x0)%nat.
 eapply IHl; try eassumption.
 omega.
 Qed.

  (* We now have a graph that we can cluster. *)


  (* The type of ILP variables *)
  Inductive Var : Type
   := SameCluster : (V * V) -> Var
    | Pi          :      V  -> Var.

  Definition Pairs : list (V * V)
   := selfcross Vs.

  Lemma All_Pairs: forall i j,
      i <> j ->
      In (i,j) Pairs \/ In (j,i) Pairs.
  Proof.
   unfold Pairs. intros.
   apply selfcross__In; try assumption; apply All_Vs.
  Qed.


  Lemma Pairs_Only_Once i j pre post l:
    In i l -> In j l -> i <> j ->
    TopSort l ->
    selfcross l = (pre ++ [(i,j)] ++ post) ->
    ~ In (i,j) post.
  Proof.
   intros HInI HInJ HNe HTop HCross.
   gen pre post.
   induction l; intros.
    destruct pre; inverts HCross.
    
   inverts HTop.
   
   inverts HInI; inverts HInJ; try (destruct HNe; reflexivity).
   
   simpl in *.
   assert (In (i,j) (selfcross_go i l)) by (apply selfcross_go__In; assumption).
   assert (~In (i,j) (selfcross l)) by (apply selfcross_Not; assumption).
   (* TODO *)
  Admitted.



 (* N is the number of nodes *)

  Definition N : Z
   := Z_of_nat (length Vs).


 (* The objective function is simply to minimise all clusters with equal weight *)
 Definition Objective : Linear Var
  := let clusters
          := map (fun p => var1 (SameCluster p)) Pairs
     in  fold_left (fun x y => x |+| y) clusters (const _ 0).


 (* Define constraint for pair of nodes *)
 Definition ConstraintOfPair (vv : V * V) : list (C Var)
  := let Sc     := SameCluster vv in
     let ScR    := match vv with
                   | (i,j) => SameCluster (j,i)
                   end in
     let ScReq  := var1 Sc |==| var1 ScR in
     let Bounds := const _ 0 |<=| var1 Sc |<=| const _ 1 in
     match (vv, E vv) with
       (* No edge *)
         | ((i,j), None)
           (* If SameCluster i j, then Pi i = Pi j *)
           => constrs
            [ var (-N) Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds
            ; ScReq ]
       (* A fusible edge *)
         | ((i,j), Some Fusible)
           => constrs
            [ var1     Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds
            ; ScReq ]
       (* A non-fusible edge *)
         | ((i,j), Some Nonfusible)
           (* SameCluster i j = 0, and Pi i < Pi j *)
           => constrs
            [ var1 (Pi i) |<| var1 (Pi j)
            ; var1 Sc |==| const _ 1
            ; ScReq ]
         end.


 Definition Constraints : list (C Var)
  := constrs (map ConstraintOfPair Pairs).

 (* There exists at least one valid clustering *)
 (* (and it's no fusion at all) *)
 Definition Sat := fun x =>
  match x with
  (* a pair of nodes not in same cluster *)
  | SameCluster p
  => 1
  (* pi is index in topological sort *)
  | Pi i
  => match index_of V_eq_dec i Vs with
     | Some n => Z_of_nat n
     | None   => 0
     end
  end.

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
    validate; Z_simp_all; try omega;
    try rewrite Hixi;
    try rewrite Hixj;
  try assert (ixi < ixj)%nat by (eapply Edge__TS_index_gt; eauto);
  try omega.

 unfold N in *.
 destruct (Z.of_nat (length Vs)); omega.

 unfold N in *.
 destruct (Z.of_nat (length Vs)).
 omega.
 simpl.
 assert (Z.neg p = - Z.pos p).
  simpl. reflexivity.
 rewrite H5. omega.

 assert (Z.neg p = - Z.pos p).
  auto.
 simpl.
 rewrite H5 in *.
 omega.

 unfold N in *.
 destruct (Z.of_nat (length Vs));
 omega.
 Qed.

 Definition Min := MinimalExists Objective Sat_Valid.


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

  remember ((fun x =>
   match x with
   | SameCluster (a,b)
   => if   Sumbool.sumbool_and _ _ _ _ (V_eq_dec a i) (V_eq_dec b j)
      then 0
      else if   Sumbool.sumbool_and _ _ _ _ (V_eq_dec a j) (V_eq_dec b i)
      then 0
      else a0 x
   | _ => a0 x end) : Assignment Var) as b.


  assert (a0 (SameCluster (i,j)) = 0 \/ a0 (SameCluster (i,j)) = 1) as HSc01.
   eapply V__Sc_Bool; assumption.
  assert (a0 (SameCluster (i,j)) = a0 (SameCluster (j,i))) as HScRefl.
   eapply V__Sc_refl; assumption.

  clear All_Vs VsTS v.

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
       unfold ConstraintOfPair.
       remember (E (i,j)) as Edge.
       destruct Edge; try destruct e; simpl;
       try (
      validate; simpl;
       simpl;
       try destruct (Sumbool.sumbool_and _ _ _ _ (V_eq_dec i i) (V_eq_dec j j)) as [Hi | Hi];
       try destruct (Sumbool.sumbool_and _ _ _ _ (V_eq_dec j j) (V_eq_dec i i)) as [Hj | Hj];
       try destruct (Sumbool.sumbool_and _ _ _ _ _ _) as [Hk | Hk];
       try destruct Hi as [Hi1 Hi2];
       try destruct Hi as [Hi | Hi];
       try (destruct Hi; reflexivity);
       try (destruct Hj; destruct H; reflexivity);
       omega).
      
      assert (a0 (Pi i) < a0 (Pi j)).
       destruct HVal.
       unfold ConstraintOfPair in H.
       simpl in H.
       rewrite <- HeqEdge in H.
       crunch_valid H.
       omega.
      omega.
      
     assert (~ In (i,j) l).
      eapply Pairs_Only_Once.
      skip.
     
      
     simpl.


      validate; simpl;
       simpl;
       try destruct (Sumbool.sumbool_and _ _ _ _ (V_eq_dec i i) (V_eq_dec j j)) as [Hi | Hi];
       try destruct (Sumbool.sumbool_and _ _ _ _ (V_eq_dec j j) (V_eq_dec i i)) as [Hj | Hj];
       try destruct (Sumbool.sumbool_and _ _ _ _ _ _) as [Hk | Hk];
       try destruct Hi as [Hi1 Hi2];
       try destruct Hi as [Hi | Hi];
       try (destruct Hi; reflexivity);
       try (destruct Hj; destruct H; reflexivity);
       try omega.
       
   destruct HVal.
   apply IHl.
   
   
Qed.
  
*)

(*
 Lemma V__Sc_trans (a : Assignment Var) Vs i j k:
   Valid (Constraints Vs) a ->
   In (i,k) (Pairs Vs)      ->
   a (SameCluster (i,j)) = 0 /\ a (SameCluster (j,k)) = 0 ->
   a (SameCluster (i,k)) = 0.
 Proof.
  intros HVal HInIK HSame.
   unfold Constraints in *.

  assert (a (SameCluster (i,k)) = 0 \/a (SameCluster (i,k)) = 1) as HBool.
   eapply V__Sc_Bool; eassumption.

   induction (Pairs Vs).
    inversion HInIK.
   simpl in *.

   apply Valid_app_and in HVal.
   destruct HVal  as [HVij HVrest].
   destruct HSame as [HSameIJ HSameJK].

   destruct HInIK.
   subst.
   unfold ConstraintOfPair in HVij.
      destruct (E (i,k)) as [e|]; try destruct e;
       crunch_valid HVij.
   destruct HBool.
    assumption.
   *)
End Untyped.
