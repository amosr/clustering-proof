Require Import Clustering.ILP.Base.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.


Section Linear.
 Variable V : Type.

 Definition const (n : Z) : Linear V
  := ([], n).

 Definition var (n : Z) (v : V) : Linear V
  := ([(n, v)], 0).

 Definition var1 := var 1.

 Definition plus (a b : Linear V) :=
 match (a,b) with
 | ((vs1,n1), (vs2, n2)) => (vs1 ++ vs2, n1 + n2)
 end.

 Definition mul (a : Linear V) (b : Z) :=
 match a with
 | (vs1,n1) => (map (fun x => match x with | (n,v) => (n * b, v) end) vs1, n1 * b)
 end.


 Definition negate (a : Linear V) :=
 match a with
 | (vs1,n1) => (map (fun x => match x with  | (n,v) => (-n, v) end) vs1, -n1)
 end.



 Lemma value_app_plus a b ass:
   value (plus a b) ass =
   value a ass   + value b ass.
 Proof.
  destruct a.
  destruct b.
  induction l.
   simpl. omega.
  destruct a.
  simpl in *.
  omega.
 Qed.

End Linear.

