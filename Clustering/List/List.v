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
    | (x::xs') => selfcross_go x xs'
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
