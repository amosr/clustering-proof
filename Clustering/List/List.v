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
