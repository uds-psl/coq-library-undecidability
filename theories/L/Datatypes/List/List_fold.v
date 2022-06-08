From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List_enc LBool.

Section forallb. 
  Variable (X : Type).
  Context (H : encodable X).

  Global Instance term_forallb : computable (@forallb X). 
  Proof.
    extract.
  Qed. 

End forallb.

Section foldl_time.
  Context {X Y : Type}.
  Context {H : encodable X}.
  Context {F : encodable Y}.

  Global Instance term_fold_left :
    computable (@fold_left X Y). 
  Proof.
    extract.
  Qed. 
End foldl_time.

Section foldr_time.
  Context {X Y: Type}.
  Context {H:encodable X}.
  Context {H0: encodable Y}.

  Global Instance term_fold_right : computable (@fold_right X Y).
  Proof.
    extract.
  Qed. 
End foldr_time.