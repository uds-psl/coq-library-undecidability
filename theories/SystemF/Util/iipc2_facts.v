(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.

(* intuitionistic implicational propositional calculus of order 2  *)
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2I {Gamma P t} : typing Gamma P t -> iipc2 Gamma t.
Proof. move=> ?. eexists. by eassumption. Qed.

Lemma iipc2_weakening {Gamma Gamma' t} : 
  incl Gamma Gamma' -> iipc2 Gamma t -> iipc2 Gamma' t.
Proof. by move=> /incl_nth_error [?] /typing_ren_term' H [?] /H /iipc2I. Qed.

(* generalized weakening in case if every assumption is derivable *)
Lemma iipc2_generalization {Gamma Gamma' t} : 
  Forall (iipc2 Gamma') Gamma -> iipc2 Gamma t -> iipc2 Gamma' t.
Proof.
  move=> H [P HP]. elim: P Gamma Gamma' t HP H.
  - move=> > /typingE /nth_error_In. rewrite Forall_forall.
    by move=> + H => /H.
  - move=> ? IH1 ? IH2 > /typingE [?] [/IH1{}IH1 /IH2{}IH2].
    move=> /[dup] [/IH1 [? ?] /IH2 [? ?]]. eexists. apply: typing_app; by eassumption. 
  - move=> s > IH Gamma Gamma' > /typingE [?] [->] /IH.
    move=> /(_ (s :: Gamma')) + HG. apply: unnest.
    { 
      constructor.
      - exists (var 0). by apply: typing_var.
      - move: HG. apply: Forall_impl. move=> ?. 
        apply: iipc2_weakening => ? /=. clear. by firstorder done.
    }
    move=> [? ?]. eexists. apply: typing_abs. by eassumption.
  - move=> ? IH > /typingE [?] [->] /IH{}IH /IH [? ?].
    eexists. apply: typing_ty_app. by eassumption. 
  - move=> > IH Gamma Gamma' > /typingE [?] [->] /IH. 
    move=> /(_ (map (ren_poly_type S) Gamma')) + HG. apply: unnest.
    {
      rewrite Forall_map. apply: Forall_impl HG.
      move=> ? [Q]. eexists. apply: typing_ren_poly_type. by eassumption.
    }
    move=> [? ?]. eexists. apply: typing_ty_abs. by eassumption.
Qed.

Lemma iipc2_poly_arrE {Gamma s t}: iipc2 Gamma (poly_arr s t) -> iipc2 (s :: Gamma) t.
Proof.
  move=> [?] /(@typing_ren_term' S) => /(_ (s :: Gamma) ltac:(done)).
  move=> /typing_app => /(_ (var 0)) H. eexists. apply: H. by apply: typing_var.
Qed.

Corollary last_poly_var_typingI {t Gamma}: 
  (if last_poly_var t is Some x then In (poly_var x) Gamma else False) -> iipc2 Gamma t.
Proof.
  move Hox: (last_poly_var t) => ox Hx. case: ox Hox Hx; last done.
  move=> x. elim: t x Gamma.
  - move=> /= > [->] /In_nth_error [? ?]. eexists. apply: typing_var. by eassumption.
  - move=> ? _ ? IH > /= /IH H /H [P]. move=> /(@typing_ren_term' S) HP. eexists.
    apply: typing_abs. by apply: HP.
  - move=> s + x Gamma /= => /(_ (S x) (map (ren_poly_type S) Gamma)).
    case: (last_poly_var s); last done. move=> [|y]; first done.
    move=> + [?] ?. subst y. rewrite in_map_iff.
    apply: unnest; first done. apply: unnest.
    { eexists. constructor; last by eassumption. done. }
    move=> [?] /typing_ty_abs ?. eexists. by eassumption.
Qed.

(* deriving arrow composition *)
Lemma iipc2_poly_arr_comp {Gamma s r t} : iipc2 Gamma (poly_arr s r) -> iipc2 Gamma (poly_arr r t) -> 
  iipc2 Gamma (poly_arr s t).
Proof.
  move=> [?] /(@typing_ren_term' S) HP1 [?] /(@typing_ren_term' S) HP2. 
  eexists. apply: typing_abs. apply: typing_app; first by apply: HP2.
  apply: typing_app; first by apply: HP1.
  by apply: (typing_var (x := 0)).
Qed.

Lemma Forall2_typing_Forall_iipc2 {Gamma Ps ts} : Forall2 (typing Gamma) Ps ts -> Forall (iipc2 Gamma) ts.
Proof. elim; [by constructor | by move=> > /iipc2I; constructor]. Qed.

(* iipc2 is preserved under type renamings *)
Lemma iipc2_ren_poly_type {Gamma t} ξ : iipc2 Gamma t -> 
  iipc2 (map (ren_poly_type ξ) Gamma) (ren_poly_type ξ t).
Proof. by move=> [?] /(typing_ren_poly_type ξ) /iipc2I. Qed.

Lemma iipc2_var_InI {Gamma t} : In t Gamma -> iipc2 Gamma t.
Proof. move=> /In_nth_error [?] /typing_var ?. eexists. by eassumption. Qed.

Lemma iipc2_poly_arrI {Gamma s t} : iipc2 (s :: Gamma) t -> iipc2 Gamma (poly_arr s t).
Proof. move=> [?] /typing_abs ?. eexists. by eassumption. Qed.

Lemma iipc2_poly_absI (x: nat) {Gamma t} : 
  Forall (fresh_in x) Gamma -> fresh_in (S x) t ->
  iipc2 Gamma (ren_poly_type (scons x id) t) -> 
  iipc2 Gamma (poly_abs t).
Proof.
  pose ξ := fun y => if PeanoNat.Nat.eq_dec x y then 0 else S y.
  move=> HG Ht /(iipc2_ren_poly_type ξ).
  have -> : map (ren_poly_type ξ) Gamma = (map (ren_poly_type S) Gamma).
  {
    elim: Gamma HG; first done.
    move=> s Gamma H /Forall_cons_iff [Hx /H{H} /= ->].
    congr cons. apply: ext_ren_poly_type_allfv_poly_type.
    apply: allfv_poly_type_impl Hx => ? ?. rewrite /ξ. by case: (PeanoNat.Nat.eq_dec _ _).
  }
  move=> [?] /typing_ty_abs /iipc2I. congr iipc2. congr poly_abs.
  rewrite poly_type_norm /ξ /= ren_poly_type_allfv_id; last done.
  apply: allfv_poly_type_impl Ht. clear.
  move=> [|y]; case: (PeanoNat.Nat.eq_dec _ _); move=> /=; by lia.
Qed.

Lemma iipc2_poly_varI x {Gamma ts ss y} : 
  nth_error Gamma x = Some (many_poly_abs (length ts) (many_poly_arr ss (poly_var (length ts + y)))) ->
  Forall (iipc2 Gamma) (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss) ->
  iipc2 Gamma (poly_var y).
Proof.
  move=> /typing_var /typing_many_ty_appI => /(_ ts ltac:(done)).
  rewrite subst_poly_type_many_poly_arr /subst_poly_type -rev_length fold_right_length_ts -/subst_poly_type.
  move=> /iipc2I. move: (map _ ss) => {}ss. move: (poly_var y) => t.
  elim: ss t; first done.
  by move=> s ss IH t /= [?] /typing_app H /Forall_cons_iff [[?] /H{H} /iipc2I /IH].
Qed.
