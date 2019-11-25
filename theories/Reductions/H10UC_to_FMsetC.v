(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform H10 constraint solvability (H10UC)
  via:
    Finite multiset term constraint solvability (FMsetTC)
  to:
    Finite multiset constraint solvability (FMsetC)
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC Problems.H10UC Problems.Reduction.

From Undecidability Require Import 
  FMset.FMsetTC FMset.mset_utils FMset.mset_eq_utils FMset.mset_term_utils.
Import NatNat.

Fixpoint term_to_tree (t: mset_term) : tree :=
  match t with
  | mset_term_zero => node 0 leaf leaf
  | mset_term_var x => node 1 (node x leaf leaf) leaf
  | mset_term_plus t u => node 2 (term_to_tree t) (term_to_tree u)
  | mset_term_h t => node 3 (term_to_tree t) leaf
  end.

Fixpoint tree_to_term (t: tree) : mset_term :=
  match t with
  | node 0 leaf leaf => mset_term_zero
  | node 1 (node x leaf leaf) leaf => mset_term_var x
  | node 2 t u => mset_term_plus (tree_to_term t) (tree_to_term u)
  | node 3 t leaf => mset_term_h (tree_to_term t)
  | _ => mset_term_zero
  end.

Definition term_to_nat (t: mset_term) : nat :=
  tree_to_nat (term_to_tree t).

Definition nat_to_term (n: nat) : mset_term :=
  tree_to_term (nat_to_tree n).

Lemma nat_term_cancel {t} : nat_to_term (term_to_nat t) = t.
Proof.
  rewrite /nat_to_term /term_to_nat nat_tree_cancel. elim: t.
  - done.
  - done.
  - by move=> t + u /= => -> ->.
  - by move=> t /= => ->.
Qed. 

(* decompose mset_term into elementary constraints *)
Fixpoint term_to_msetcs (t: mset_term) : list msetc :=
  match t with
  | mset_term_zero => [msetc_zero (term_to_nat t)]
  | mset_term_var x => []
  | mset_term_plus u v => 
      [msetc_sum (term_to_nat t) (term_to_nat u) (term_to_nat v)] ++ 
      (term_to_msetcs u) ++ (term_to_msetcs v)
  | mset_term_h u => 
      [msetc_h (term_to_nat t) (term_to_nat u)] ++ (term_to_msetcs u)
  end.

Definition encode_eq (t u: mset_term) :=
  [(msetc_sum (tree_to_nat leaf) (tree_to_nat leaf) (tree_to_nat leaf)); 
  (msetc_sum (term_to_nat t) (tree_to_nat leaf) (term_to_nat u))].

(* encode FMsetC_PROBLEM as LPolyNC_PROBLEM *)
Definition encode_problem (msetcs : FMsetTC_PROBLEM) : FMsetC_PROBLEM :=
  flat_map (fun '(t, u) => (encode_eq t u) ++ term_to_msetcs t ++ term_to_msetcs u) msetcs.

Lemma Forall_flat_mapP {X Y: Type} {P: Y -> Prop} {f: X -> list Y} {A: list X}: 
  Forall P (flat_map f A) <-> Forall (fun a => Forall P (f a)) A.
Proof.
  elim: A.
    move=> /=. by constructor.
  move=> a A IH. by rewrite /flat_map -/(flat_map _ _) ? Forall_norm IH.
Qed.

Lemma term_to_nat_pos {t} : term_to_nat t = S (Nat.pred (term_to_nat t)).
Proof.
  case: t; by move=> *. 
Qed.

Lemma completeness {l} : FMsetTC_SAT l -> FMsetC_SAT (encode_problem l).
Proof.
  move=> [φ]. rewrite -mset_satP => Hφ.
  pose ψ x := if x is 0 then [] else mset_sem φ (nat_to_term x).
  have Hψ (A) : Forall (msetc_sem ψ) (term_to_msetcs A).
  {
    elim: A.
    - by rewrite /term_to_msetcs ? Forall_norm /ψ.
    - by rewrite /term_to_msetcs.
    - move=> A IHA B IHB. 
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      constructor; first last.
        by constructor.
      rewrite /ψ /msetc_sem ? nat_term_cancel.
      by rewrite ? term_to_nat_pos.
    - move=> A IH. 
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      constructor; last done.
      rewrite /ψ /msetc_sem ? nat_term_cancel.
      by rewrite ? term_to_nat_pos.
  }
  exists ψ.
  rewrite - Forall_forall /encode_problem Forall_flat_mapP.
  apply: Forall_impl; last eassumption. 
  move=> [A B]. rewrite ? Forall_norm.
  move=> HφAB. constructor; first last.
    by constructor.
  constructor.
    done.
  rewrite /ψ /msetc_sem.
  rewrite (@term_to_nat_pos A) (@term_to_nat_pos B) /(tree_to_nat leaf).
  by rewrite - ? term_to_nat_pos ? nat_term_cancel.
Qed.

Lemma soundness {l} : FMsetC_SAT (encode_problem l) -> FMsetTC_SAT l.
Proof.
  move=> [ψ]. rewrite -Forall_forall Forall_flat_mapP => Hψ.
  pose φ x := ψ (term_to_nat (mset_term_var x)).
  exists φ. rewrite -mset_satP.
  apply: Forall_impl; last by eassumption.
  move=> [t u]. rewrite ? Forall_norm => [[+ [+]]].
  rewrite /msetc_sem -/(msetc_sem _). move=> [/eq_app_nil_nilP /copy [Hψ0 ->]].
  rewrite /app => Hψtu.

  have Hφ (s) : Forall (msetc_sem ψ) (term_to_msetcs s) -> mset_sem φ s ≡ (ψ (term_to_nat s)).
  {
    clear. elim: s.
    - rewrite /term_to_msetcs ? Forall_norm /msetc_sem /φ /mset_sem.
      by apply /eq_symm.
    - by move=> x _.
    - move=> t IHt u IHu.
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      move=> [+ [/IHt {}IHt /IHu {}IHu]].
      rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
      move /eq_symm. apply /eq_trans.
      by apply: eq_appI.
    - move=> t IH.
      rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
      move=> [+ /IH {}IH].
      rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
      move /eq_symm. apply /eq_trans.
      by apply: eq_mapI.
  }
  move=> /Hφ Ht /Hφ Hu.
  under eq_lr; by eassumption.
Qed.

(* many-one reduction from FMsetTC to FMsetC *)
Theorem FMsetTC_to_FMsetC : FMsetTC_SAT ⪯ FMsetC_SAT.
Proof.
  exists encode_problem.
  move=> cs. constructor.
    exact completeness.
  exact soundness.
Qed.

From Undecidability Require FMset.H10UC_to_FMsetTC.

Theorem H10UC_to_FMsetC : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
  apply (reduces_transitive H10UC_to_FMsetTC.H10UC_to_FMsetTC).
  apply FMsetTC_to_FMsetC.
Qed.

Check H10UC_to_FMsetC.
(* Print Assumptions H10UC_to_FMsetC. *)

From Undecidability Require Import Problems.TM.
From Undecidability Require H10C_to_H10UC.

(* undecidability of FMsetC *)
Theorem FMsetC_undec : Halt ⪯ FMsetC_SAT.
Proof.
  apply (reduces_transitive H10C_to_H10UC.H10UC_undec).
  apply H10UC_to_FMsetC.
Qed.

Check FMsetC_undec.
(* Print Assumptions H10UC_to_FMsetC. *)
