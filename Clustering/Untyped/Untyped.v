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

 Definition Constraints : list (C Var)
       (* Define constraint for pair of nodes *)
  := let constr_go vv :=
         let Sc     := SameCluster vv in
         let Bounds := const _ 0 |<=| var1 Sc |<=| const _ 1 in
         match (vv, E vv) with
       (* No edge *)
         | ((i,j), None)
           (* If SameCluster i j, then Pi i = Pi j *)
           => constrs
            [ var (-N) Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds ]
       (* A fusible edge *)
         | ((i,j), Some Fusible)
           => constrs
            [ var1     Sc |<=| var1 (Pi j) |-| var1 (Pi i) |<=| var N Sc
            ; Bounds ]
       (* A non-fusible edge *)
         | ((i,j), Some Nonfusible)
           (* SameCluster i j = 0, and Pi i < Pi j *)
           => constrs
            [ var1 (Pi i) |<| var1 (Pi j)
            ; var1 Sc |==| const _ 1 ]

         end

     in  constrs (map constr_go Pairs).



 Definition Clustering : Assignment Var -> V -> Z.
 Admitted.

 Lemma Clustering_SC : forall (a : Assignment Var) i j,
       Valid Constraints a ->
       Clustering a i = Clustering a j <->
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

End Untyped.
