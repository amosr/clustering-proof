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
