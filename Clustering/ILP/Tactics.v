Require Import Clustering.ILP.Base.


Ltac validate
 := repeat
 (match goal with
  | [ |- Valid _ _ ]
  => constructor
  | [ |- Valid_go _ _]
  => constructor
  end).


Ltac crunch_valid H
 := repeat
 (match goal with
  | [ H : Valid _ _ |- _ ]
  => inversion H; clear H
  | [ H : Valid_go _ _ |- _]
  => inversion H; clear H
  end); subst.


