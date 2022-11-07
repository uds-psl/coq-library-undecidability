From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List.List_enc LBool LNat.

#[global]
Instance termT_append X {intX : encodable X} : computable (@List.app X).
Proof.
  extract.
Qed.

  
#[global]
Instance term_map (X Y:Type) (Hx : encodable X) (Hy:encodable Y): computable (@map X Y).
Proof.
  extract.
Defined. (*because other extract*)
  

#[global]
Instance termT_rev_append X `{encodable X}: computable (@rev_append X).
Proof.
extract.
Qed.

#[global]
Instance termT_rev X `{encodable X}: computable (@rev X).
Proof.
eapply computableExt with (x:= fun l => rev_append l []).
{intro. rewrite rev_alt. reflexivity. }
extract.
Qed.

Section Fix_X.
  Variable (X:Type).
  Context {intX : encodable X}.

  Global Instance term_filter_notime: computable (@filter X).
  Proof using intX.
    extract.
  Defined. (*because other extract*)

  Global Instance term_repeat: computable (@repeat X).
  Proof using intX.
    extract.
  Qed.
  
End Fix_X.
