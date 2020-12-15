(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    System F Typability (SysF_TYP)
  to:
    System F Typechecking (SysF_TC)
*)

Require Import List Lia Relation_Operators.
Import ListNotations.
Require Import Undecidability.SystemF.SysF.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts pure_typing_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module Argument.
Section SysF_TYP_to_SysF_TC.

Variables M0 : pure_term.

Definition Gamma_M0 := [poly_abs (poly_var 0)].

Definition M_M0 := pure_app (pure_var 0) (many_pure_term_abs (pure_var_bound M0) M0).

Definition t_M0 := poly_var 0.

(* overall, we show that M0 is typable iff Gamma_M0 ⊢ M_M0 : t_M0 holds *)

(* typability to type checking *)
Lemma transport : 
  SysF_TYP M0 -> SysF_TC (Gamma_M0, M_M0, t_M0).
Proof.
  move=> [Gamma] [t] /pure_typing_iff_type_assignment.
  move=> /pure_typableI /pure_typable_many_pure_term_abs_allI [{}t].
  move=> /(pure_typing_ren_pure_term id (Delta := Gamma_M0)). rewrite ren_pure_term_id.
  apply: unnest; first by case.
  move=> /(pure_typing_pure_app_simpleI (M := pure_var 0) (t := t_M0)).
  apply: unnest.
  { apply: (pure_typing_pure_var 0); first by reflexivity. 
    apply: rt_step. by apply: contains_step_subst. }
  move=> /pure_typing_to_typing /= [P] [HP] /typing_to_type_assignment.
  by rewrite -HP.
Qed.

(* type checking to typability *)
Lemma inverse_transport : 
  SysF_TC (Gamma_M0, M_M0, t_M0) -> SysF_TYP M0.
Proof.
  move=> /pure_typing_iff_type_assignment. rewrite /Gamma_M0 /M_M0 /t_M0.
  move=> /pure_typingE' [?] [?] [_] [/pure_typableI HM0 _].
  have : exists Gamma, pure_typable Gamma M0.
  {
    elim: (pure_var_bound M0) ([poly_abs (poly_var 0)]) HM0.
    - move=> /= ? ?. eexists. by eassumption.
    - by move=> {}n IH Gamma /= /pure_typableE [?] /IH.
  }
  move=> [Gamma] [t] /pure_typing_to_typing [P] [->].
  move=> /typing_to_type_assignment ?. by exists Gamma, t.
Qed.

End SysF_TYP_to_SysF_TC.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* System F Typability many-one reduces to System F Type Checking *)
Theorem reduction : SysF_TYP ⪯ SysF_TC.
Proof.
  exists (fun 'M0 => (Argument.Gamma_M0, Argument.M_M0 M0, Argument.t_M0)).
  move=> M0. constructor.
  - exact: Argument.transport.
  - exact: Argument.inverse_transport.
Qed.
