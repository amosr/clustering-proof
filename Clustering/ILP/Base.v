Require Import Omega.
Set Implicit Arguments.

Section ILP.

(* type of variables *)
Variable V : Type.

(* linear coefficients of variables *)
Inductive L : Type
  := Lv : V -> nat -> L
    | Lc : nat -> L.

(* constraints *)
Inductive C : Type
  := Le : L -> L -> C.
 (*   | Le : L -> L -> C
    | Between : L -> L -> L -> C.
*)

Variable Objective : list L.
Variable Constraints : list C.

Definition Assignment := V -> nat.

Inductive Valid_c (a : Assignment) : C -> Prop
 := Valid_c_vv : forall v1 n1 v2 n2,
                     a v1 * n1 <= a v2 * n2 ->
                     Valid_c a (Le (Lv v1 n1) (Lv v2 n2))
  |  Valid_c_vn : forall v1 n1 n2,
                     a v1 * n1 <= n2 ->
                     Valid_c a (Le (Lv v1 n1) (Lc n2))
  |  Valid_c_nv : forall n1 v2 n2,
                     n1 <= a v2 * n2 ->
                     Valid_c a (Le (Lc n1) (Lv v2 n2))
  |  Valid_c_nn : forall n1 n2,
                     n1 <= n2 ->
                     Valid_c a (Le (Lc n1) (Lc n2)).

Inductive Valid_go (a : Assignment) : list C -> Prop
 := Valid_go_nil : Valid_go a nil
   | Valid_go_ceq :
      forall c cs, Valid_c a c -> Valid_go a cs -> Valid_go a (c::cs).

Definition Valid (a : Assignment) : Prop
 := Valid_go a Constraints.

Hypothesis Sat : Assignment.

Fixpoint obj_go (os : list L) (a : Assignment) : nat 
 := match os with
      | nil => 0
      | cons (Lv v n) os' => a v * n + obj_go os' a
      | cons (Lc n) os' => n + obj_go os' a
      end.

Definition obj (a : Assignment) : nat
 := obj_go Objective a.

Inductive Minimal
 := MinimalC : forall a, Valid a -> (forall b, Valid b -> obj a <= obj b)
              -> Minimal.

Axiom MinimalExists : Valid Sat -> Minimal.

Definition assignmentOfMinimal (m : Minimal) : Assignment :=
 match m with
  | MinimalC a _ _  => a
 end.

End ILP.
