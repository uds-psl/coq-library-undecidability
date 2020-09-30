(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.Facts Undecidability.SystemF.Util.poly_type_facts.

Require Import ssreflect ssrbool ssrfun.

(* evaluates predicate p on all free variables *)
Fixpoint allfv_pure_term (p: nat -> Prop) (M: pure_term) :=
  match M with
  | pure_var x => p x
  | pure_app M N => allfv_pure_term p M /\ allfv_pure_term p N
  | pure_abs M => allfv_pure_term (scons True p) M
  end.
  
Lemma allfv_pure_term_impl {p1 p2: nat -> Prop} {M}: 
  (forall x, p1 x -> p2 x) -> allfv_pure_term p1 M -> allfv_pure_term p2 M.
Proof.
  elim: M p1 p2.
  - move=> >. by apply.
  - by move=> ? IH1 ? IH2 > /= /copy [/IH1 {}IH1 /IH2 {}IH2] [/IH1 ? /IH2 ?].
  - move=> > IH > H /=. apply: IH. by case.
Qed.

Lemma allfv_pure_term_ren_pure_term {p ξ M} : 
  allfv_pure_term p (ren_pure_term ξ M) <-> allfv_pure_term (ξ >> p) M.
Proof.
  elim: M ξ p.
  - done.
  - move=> ? IH1 ? IH2 > /=. by rewrite IH1 IH2.
  - move=> ? IH > /=. rewrite IH. constructor; apply: allfv_pure_term_impl; by case.
Qed.

Lemma allfv_pure_term_TrueI {p: nat -> Prop} {M} : (forall x, p x) -> allfv_pure_term p M.
Proof.
  move=> Hp. elim: M.
  - move=> > /=. by apply: Hp.
  - by move=> ? + ? + /=.
  - move=> ? /=. apply: allfv_pure_term_impl. case; first done.
    move=> *. by apply: Hp.
Qed.

Lemma ren_pure_term_id {M} : ren_pure_term id M = M.
Proof.
  elim: M.
  - done.
  - move=> /=. congruence.
  - move=> /=. rewrite /upRen_pure_term_pure_term.
    move=> > ?. under extRen_pure_term => ? do rewrite up_ren_id. by congruence.
Qed.

Lemma ren_pure_term_id' {ξ M} : (forall x, ξ x = x) -> ren_pure_term ξ M = M.
Proof. move=> ?. rewrite -[RHS]ren_pure_term_id. by apply: extRen_pure_term. Qed.

Fixpoint pure_var_bound (M: pure_term) :=
  match M with
  | pure_var x => 1 + x
  | pure_app M N => 1 + pure_var_bound M + pure_var_bound N
  | pure_abs M => 1 + pure_var_bound M
  end.

Lemma pure_var_boundP M : allfv_pure_term (gt (pure_var_bound M)) M.
Proof.
  elim: M.
  - move=> /=. by lia.
  - move=> ? IH1 ? IH2 /=. constructor; [move: IH1 | move: IH2]; apply: allfv_pure_term_impl; by lia.
  - move=> ? /=. apply: allfv_pure_term_impl. case; first done. move=> /=. by lia.
Qed.
