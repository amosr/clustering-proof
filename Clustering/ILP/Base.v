Require Export Omega.
Set Implicit Arguments.

Global Close Scope nat.
Global Open Scope Z.

Section ILP.

(* type of variables *)
Variable V : Type.

(* linear coefficients of variables *)
Definition VC : Type := (Z * V)%type.

(* A linear function is a bunch of variables with coefficients, and a constant *)
Definition Linear : Type
 := (list VC * Z)%type.

(* constraints *)
Inductive C : Type
  := Le : Linear -> Linear -> C.

(* We don't actually need a strictly less than, since we're operating on nats *)
(*   | Lt : L -> L -> C *)


(* A variable assignment is a mapping from variable to Z *)
Definition Assignment := V -> Z.

(* Find a linear function's value, for given assignment  *)
Fixpoint value_go (os : list VC) (a : Assignment) : Z
 := match os with
      | nil => 0
      | cons (n,v) os' => a v * n + value_go os' a
      end.

Definition value (l : Linear) (a : Assignment) : Z
 := match l with
     | (os, c) => value_go os a + c
     end.


(* An assignment is valid for a list of constraints iff all lhs values are less than or equal to rhs *)
Inductive Valid_go (a : Assignment) : list C -> Prop
 := Valid_go_nil : Valid_go a nil
   | Valid_go_cons :
      forall l1 l2 cs, value l1 a <= value l2 a -> Valid_go a cs -> Valid_go a (Le l1 l2 ::cs).


Variable Objective : Linear.
Variable Constraints : list C.

Definition Valid (a : Assignment) : Prop
 := Valid_go a Constraints.

Hypothesis Sat : Assignment.

Definition obj := value Objective.

Inductive Minimal
 := MinimalC : forall a, Valid a -> (forall b, Valid b -> obj a <= obj b)
              -> Minimal.

Axiom MinimalExists : Valid Sat -> Minimal.

Definition assignmentOfMinimal (m : Minimal) : Assignment :=
 match m with
  | MinimalC a _ _  => a
 end.

End ILP.
