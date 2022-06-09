From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List.List_enc LBool LNat LOptions.
From Undecidability.Shared.Libs.PSL.Lists Require Export Filter.

#[global]
Instance termT_append X {intX : registered X} : computable (@List.app X).
Proof.
  extract.
Qed.
  
#[global]
Instance term_map (X Y:Type) (Hx : registered X) (Hy:registered Y): computable (@map X Y).
Proof.
  extract.
Qed.

#[global]
Instance termT_rev_append X `{registered X}: computable (@rev_append X).
Proof.
  extract.
Qed.

#[global]
Instance termT_rev X `{registered X}: computable (@rev X).
Proof.
  eapply computableExt with (x:= fun l => rev_append l []).
  {intro. rewrite rev_alt. reflexivity. }
  extract.
Qed.

(* seq *)
#[global]
Instance term_seq : computable seq. 
Proof. 
  extract.
Qed. 

Section Fix_X.
  Variable (X:Type).
  Context {intX : registered X}.

  Global Instance term_filter_notime: computable (@filter X).
  Proof using intX.
    extract.
  Qed. (*because other extract*)

  Global Instance term_repeat: computable (@repeat X).
  Proof using intX.
    extract.
  Qed.
  
End Fix_X.

#[global]
Instance termT_nth_error (X:Type) (Hx : registered X): computable (@nth_error X). 
Proof.
  extract.
Qed.

#[global]
Instance termT_length X `{registered X} : computable (@length X).
Proof.
  extract.
Qed.

#[global]
Instance term_nth X (Hx : registered X) : computable (@nth X). 
Proof.
  extract.
Qed.

(* prodLists *)
Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : registered X} `{Yint : registered Y}.

  #[global]
  Instance term_prodLists : computable (@list_prod X Y). 
  Proof. 
    apply computableExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end).
    1: { unfold list_prod. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract. 
  Qed.
End fixprodLists. 