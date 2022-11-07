From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability.L.Datatypes Require Export List.List_enc.

Section list_in.
  Variable (X : Type). 
  Variable (eqb : X -> X -> bool). 
  Variable eqb_correct : forall a b,  a = b <-> eqb a b = true.  

  Definition list_in_decb := fix rec (l : list X) (x : X) : bool :=
  match l with [] => false
          | (l :: ls) => eqb l x || rec ls x
  end. 

  Lemma list_in_decb_iff (l : list X) : forall x, list_in_decb l x = true <-> x el l. 
  Proof using eqb_correct. 
    intros x. induction l.
    - cbn. firstorder. 
    - split. 
      + intros [H1 | H1]%orb_true_elim. left. now apply eqb_correct. 
        apply IHl in H1. now right. 
      + intros [H | H].
        cbn. apply orb_true_intro; left; now apply eqb_correct. 
        cbn. apply orb_true_intro; right; now apply IHl. 
  Qed.

  Fixpoint list_incl_decb (a b : list X) := 
    match a with 
    | [] => true
    | (x::a) => list_in_decb b x && list_incl_decb a b
    end. 


End list_in.

Section list_in_time.
  Variable (X : Type).
  Context {H : encodable X}.
  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbComp X}.

  Global Instance term_list_in_decb : computable (@list_in_decb X eqbX).
  Proof using XeqbComp Xeq. 
    extract.
  Qed. 

  Global Instance term_list_incl_decb : computable (@list_incl_decb X eqbX). 
  Proof using XeqbComp Xeq. 
    extract.
  Qed.
End list_in_time. 
