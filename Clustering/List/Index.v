Require Import Clustering.Tactics.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Section Index.
 Variable A : Type.
 Hypothesis Heqdec : forall (a b : A), {a = b} + {a <> b}.

 Fixpoint index_of (x : A) (vs : list A) : option nat
  := match vs with
     | []    => None
     | v::vs' => if   Heqdec x v
                 then Some 0
                 else match index_of x vs' with
                      | None   => None
                      | Some n => Some (S n)
                      end
     end.

 Lemma index_of__lt_length: forall a xs res,
       index_of a xs = Some res ->
       res < length xs.
 Proof.
  induction xs; intros.
   - inversion H.
   - simpl in H.
     destruct (Heqdec a a0).
     + inverts H. simpl. omega.
     + simpl.
       destruct (index_of a xs).
       assert (n0 < length xs). apply IHxs. reflexivity.
       inverts H. omega.
       inverts H.
 Qed.


 Lemma index_of__nth: forall a xs res d,
       index_of a xs = Some res ->
       nth res xs d = a.
 Proof.
  induction xs; intros.
   - inversion H.
   - simpl in H.
     destruct (Heqdec a a0).
     + inverts~ H.
     + destruct (index_of a xs); inverts H.
       applys~ IHxs.
 Qed.




 Lemma index_of__not_In: forall a xs,
       index_of a xs = None ->
       ~ In a xs.
 Proof.
  induction xs; unfold not; intros.
   - inversion H0.
   - simpl in *.
     inverts H0.
     destruct (Heqdec a a).
     inverts H.
     apply~ n.
     
     destruct (Heqdec a a0).
     inverts H.
     destruct (index_of a xs).
     inverts H.
     apply~ IHxs.
 Qed.




 Lemma In__index_of: forall a xs,
       In a xs ->
       exists n, index_of a xs = Some n.
 Proof.
  induction xs; intros.
   - inversion H.
   - simpl in *.
     inverts H.
      destruct (Heqdec a a). eauto.
      destruct n. eauto.
     apply IHxs in H0.
     destruct H0.
     rewrite H.
     destruct (Heqdec a a0); eauto.
 Qed.

End Index.

