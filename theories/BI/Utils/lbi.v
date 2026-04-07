(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8 Eqdep_dec.

From Undecidability.BI
  Require Import BI utils hil.

Import BI_notations ListNotations.

Module LBI_tactics.

  Abbreviation lft := BI_left (only parsing).
  Abbreviation rt := BI_right (only parsing).

  (* Given a bunch Γ and a list l (eg [lft;rt;lft ... ]) of
     left or right choices, outputs the context Δ[_] and the
     bunch Σ such that Δ[Σ] = Γ, corresponding to position
     of Σ in Γ given by the list of left/right choices l *)
  Ltac analyse_bunch Γ l :=
    match type of Γ with
    | BI_bunch ?mu ?pr =>
      match l with
      | nil => constr:((@BI_ctx_hole mu pr,Γ))
      | ?s::?l =>
        match Γ with
        | ?L ⊛[?k] ?R =>
          match s with
          | lft => match analyse_bunch L l with
                   | (?c,?f) => constr:((BI_ctx_comp BI_right k R c,f))
                   end
          | rt  => match analyse_bunch R l with
                   | (?c,?f) => constr:((BI_ctx_comp BI_left k L c,f))
                   end
          end 
        end
      end
    end.

  (* Use l as a list of left/right choice to put the sequent into
     the shape Δ[_] ⊦ _ depending on l *)
  Tactic Notation "focus" "at" uconstr(l) :=
    let m := constr:(l : list BI_side)
    in match goal with 
    | |- @LBI_provable ?mu ?pr ?cut ?G ?A => 
      match analyse_bunch G m with
      | (?C,?f) => change (@LBI_provable mu pr cut C[f] A)
      end
    end.

  (* Put a bunch sequent Γ ⊦ A in the shape Δ[Σ] ⊦ A using
     the location of Σ in Γ given by l, and defines
     i := Δ *)
  Tactic Notation "focus" "at" uconstr(l) "as" ident(i) :=
    focus at l;
    match goal with
    | |- @LBI_provable _ _ _ ?C[_] _ => set (i := C)
    end. 

  (* Apply a left on the hole Δ[_] given by l *)
  Tactic Notation "rule" constr(R) "at" uconstr(l) :=
    focus at l; apply R; simpl; auto.

  (* try a cut rule on the hole given by l *)
  Tactic Notation "cut" "at" uconstr(l) :=
    focus at l;
    match goal with
    | H: @LBI_provable _ _ _ ?G _ |- @LBI_provable _ _ _ _[?G] _ => apply LBI_cut with (2 := H); simpl; auto
    | H: @LBI_provable _ _ _ _ ?C |- @LBI_provable _ _ _ _[_] ?C => apply LBI_cut with (3 := H); simpl; auto
    end.

End LBI_tactics.

Import LBI_tactics.

Section LBI.

  Variables (µ : BI_conn → bool) (prop : Set) (cut : BI_cut).

  Implicit Type (Φ : BI_form µ prop → Prop).

  Notation "⊥" := (@BI_form_bot _ _ _).
  Notation "⊤" := (@BI_form_unit _ _ BI_addi _).
  Notation "1" := (@BI_form_unit _ _ BI_mult _).
  Notation "A ⇒ B" := (@BI_form_impl _ _ BI_addi _ A B) (at level 63, right associativity, format "A ⇒ B").
  Notation "A '-∗' B" := (@BI_form_impl _ _ BI_mult _ A B) (at level 63, right associativity, format "A -∗ B").
  Notation "A ∗ B" := (@BI_form_conj _ _ BI_mult _ A B) (at level 59, left associativity, format "A ∗ B").
  Notation "A ⩑ B" := (@BI_form_conj _ _ BI_addi _ A B) (at level 59, left associativity, format "A ⩑ B").
  Notation "A ⩒ B" := (@BI_form_disj _ _ _ A B) (at level 61, left associativity, format "A ⩒ B").

  Notation "A '-⊙[' k , e ']' B" := (@BI_form_impl _ _ k e A B) (at level 62, right associativity, format "A -⊙[ k , e ] B").

  Implicit Types (A B : BI_form µ prop).

  Notation "Σ '⊦' A" := (@LBI_provable µ prop cut Σ A) (at level 70, format "Σ  ⊦  A").

  Arguments BI_ctx_hole { _ _ }.

  Hint Constructors LBI_provable BI_bunch_equiv : core.

  Fact LBI_impl_left k A B (e : µ (BI_impl k) = true) :

          (*-------------------------*)
            ⟨A⟩ ⊛[k] ⟨A-⊙[k,e]B⟩ ⊦ B.

  Proof. rule LBI_impl_l at []. Qed.

  Hint Resolve LBI_impl_left : core.

  Fact LBI_wc_impl_inv k Γ A B (e : µ (BI_impl k) = true) (_ : cut = BI_with_cut) :

             Γ ⊦ A-⊙[k,e]B 
      →   (*---------------*) 
            ⟨A⟩ ⊛[k] Γ ⊦ B.
            
  Proof. intros; cut at [rt]. Qed.

  Fact LBI_wc_impl_inv' k A B (e : µ (BI_impl k) = true) (_ : cut = BI_with_cut) :

            ø[k] ⊦ A-⊙[k,e]B
      →   (*----------------*)
               ⟨A⟩ ⊦ B.

  Proof. intros ?%LBI_wc_impl_inv; eauto. Qed.

  Fact LBI_neut_l k Γ A : 

                Γ ⊦ A
      →  (*----------------*)
           ø[k] ⊛[k] Γ ⊦ A.

  Proof. eauto. Qed.

  Fact LBI_neut_l_inv k Γ A : 

           ø[k] ⊛[k] Γ ⊦ A
      →  (*---------------*)
                Γ ⊦ A.

  Proof. eauto. Qed.

  Fact LBI_neut_r k Γ A :

                 Γ ⊦ A
      →   (*----------------*)
            Γ ⊛[k] ø[k] ⊦ A.

  Proof. eauto. Qed.

  Fact LBI_neut_r_inv k Γ A :

            Γ ⊛[k] ø[k] ⊦ A
      →   (*---------------*)
                Γ ⊦ A.

  Proof. eauto. Qed.

  Fact LBI_cntr_root Γ A :
  
           Γ ⊛ₐ Γ ⊦ A
      →  (*----------*)
             Γ ⊦ A.

  Proof. intros; rule LBI_cntr at []. Qed.

  Fact LBI_impl_root Γ  k A B C (e : µ (BI_impl k) = true) :

         Γ ⊦ A     →     ⟨B⟩ ⊦ C
    →  (*-----------------------*)
         Γ ⊛[k] ⟨A-⊙[k,e]B⟩ ⊦ C.
         
  Proof. intros; rule LBI_impl_l at []. Qed.

End LBI.