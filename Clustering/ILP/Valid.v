Require Import Clustering.ILP.Base.

Require Import Clustering.Tactics.

Require Import Coq.Lists.List.
Import ListNotations.

Lemma Valid_app_and V (a : Assignment V) cs ds:
      Valid (cs ++ ds) a <->
      Valid cs a /\ Valid ds a.
Proof.
 split.

  - (* cs ++ ds -> cs /\ ds *)
    split.
   + (* cs ++ ds -> cs *)
     induction cs as [|c cs].
     * constructor. 
     * destruct c.
       inverts H.
       constructor; try apply IHcs; assumption.
   + (* cs ++ ds -> ds *)
     induction cs as [|c cs].
     * assumption.
     * apply IHcs.
       inverts H.
       assumption.

  - (* cs /\ ds -> cs ++ ds *)
    intros H.
    destruct H as [Hcs Hds].
    induction cs as [|c cs].
    + assumption.
    + inverts Hcs.
      simpl.
      constructor; try apply IHcs; assumption.
Qed.



Definition update {V} (V_eq_dec : forall a b, {a = b} + {a <> b})
           (v : V) (val : Z) (a : Assignment V) : Assignment V
 := fun x =>
     if V_eq_dec x v
     then val
     else a x.

(*
Print Linear.
Section V_eq_dec.

Definition mentions_go {V} (v : V) (c : Linear V) :=
 Contains (eq v).

Lemma Valid_update  (a : Assignment V) v val cs:
      Valid cs a ->
      Valid (mentions v cs) (update V_eq_dec v val a) ->
      Valid cs (update V_eq_dec v val a). 
*)


