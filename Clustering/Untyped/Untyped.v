(* Simplification of Megiddo's ILP clustering algorithm:
   one type, and no weights.
*)

Require Import Clustering.ILP.
Require Import Clustering.List.List.

Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

Section Untyped.
 
 (* Type of nodes *)
 Variable V : Type.

 (* Equality must be decidable *)
 Hypothesis V_eq_dec
  : forall (a b : V),
    a = b \/ a <> b.

 (* Edges may be fusible or non *)
 Inductive EdgeType : Type
  := Fusible
   | Nonfusible.

 (* Is there an edge between two? If so, what kind *)
 Variable E : (V * V) -> option EdgeType.


  Hypothesis beqV
  : V -> V -> bool.

  Hypothesis beqV__V_eq_dec
  : forall (a b : V),
    beqV a b = true <-> a = b.


 Section TopSort.
 (* There must exist a topological ordering *)
 Variable Vs : list V.
 
 Inductive TopSort : list V -> Prop
  := TS_Nil  : TopSort nil
   | TS_Cons : forall x xs,
               Forall (fun y => E (x, y) = None) xs ->
               TopSort (x::xs).

 Hypothesis VsTS : TopSort Vs.

 (* We now have a graph that we can cluster. *)


 (* The type of ILP variables *)
 Inductive Var : Type
  := SameCluster : (V * V) -> Var
   | Pi          :      V  -> Var.

 Definition Pairs : list (V * V)
  := selfcross Vs.

 (* N is the number of nodes *)

 Definition N : Z
  := Z_of_nat' (length Vs).


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

 End TopSort.

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


 Lemma V__Sc_Bool (a : Assignment Var) Vs ij :
   Valid (Constraints Vs) a ->
   In ij (Pairs Vs)         ->
   a (SameCluster ij) = 0 \/ a (SameCluster ij) = 1.
 Proof.
  intros HVal HIn.
   unfold Constraints in *.

   induction (Pairs Vs).
    inversion HIn.
   simpl in *.

   apply Valid_app_and in HVal.
   destruct HVal as [HVij HVrest].

   destruct HIn.
    - subst.
      clear IHl HVrest beqV beqV__V_eq_dec l.
      unfold ConstraintOfPair in HVij.
      destruct ij as [i j].
      destruct (E (i,j)) as [e|]; try destruct e;
               crunch_valid HVij; omega.

    - apply IHl; assumption.
Qed.


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

End Untyped.
