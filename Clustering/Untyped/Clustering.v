Require Import Clustering.ILP.
Require Import Clustering.List.List.
Require Import Clustering.Tactics.
Require Import Clustering.Untyped.Untyped.

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


 Hypothesis beqV
  : V -> V -> bool.

 Hypothesis beqV__V_eq_dec
  : forall (a b : V),
    beqV a b = true <-> a = b.

 Definition Var := Var V.

 Variable Vs : list V.
 Definition Pairs := Pairs Vs.




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

