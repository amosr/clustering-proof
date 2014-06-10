Require Import Clustering.ILP.
Require Import Clustering.Untyped.Untyped.

Extraction Language Haskell.

Extract Constant Clustering.ILP.Base.MinimalExists => "glpk_find_minimal".

Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive sumor => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].
Extract Inductive CompareSpecT => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Open Scope Z.

Extract Inductive nat => "Prelude.Int" [ "0" "(Prelude.+ 1)" ]
"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive Z => "Prelude.Int" [ "0" "(0 Prelude.+)" "Prelude.negate" ]
"(\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inductive positive => "Prelude.Int" [ "((Prelude..) (Prelude.+ 1) (Prelude.* 2))" "(Prelude.* 2)" "1" ]
"(\fI fO fH n -> if n Prelude.== 1 then fH n else if n `Prelude.mod` 2 Prelude./= 0 then fI (n Prelude.- 1 `Prelude.div` 2) else fO (n `Prelude.div` 2))".


Extract Constant Pos.add => "(Prelude.+)".
Extract Constant Peano.plus => "(Prelude.+)".
Extract Constant Z.add => "(Prelude.+)".

Extract Constant Pos.mul => "(Prelude.*)".
Extract Constant mult => "(Prelude.*)".
Extract Constant Z.mul => "(Prelude.*)".

Extract Constant Z.div => "Prelude.div".


Extraction "extract/Untyped" Constraints Objective.
