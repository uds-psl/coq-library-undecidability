Require Import List Lia.

From Undecidability.Synthetic Require Import Undecidability.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_nat.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From Undecidability.H10 
  Require Import Dio.dio_single H10 Diophantine.

From Undecidability.MuRec.Util 
  Require Import recalg ra_dio_poly MuRec_computable ra_sem_eq ra_recomp.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Lemma vec_pos_spec {X} {n} (v : Vector.t X n) (i : Fin.t n) :
  vec_pos v i = Vector.nth v i.
Proof.
  induction v; cbn; f_equal.
  - inversion i.
  - eapply (Fin.caseS' i); cbn; eauto.
Qed.

Fixpoint dio_move {k k'} (P : dio_polynomial (pos k) (pos (S k'))) : dio_polynomial (pos (S k)) (pos k') :=
  match P with
  | dp_nat n => dp_nat n
  | dp_var n => dp_var (Fin.FS n)
  | dp_par p => Fin.caseS' p _ (dp_var (Fin.F1)) dp_par
  | dp_comp op P1 P2 => dp_comp op (dio_move P1) (dio_move P2)
  end.

Lemma dio_move_spec {k k'} (P : dio_polynomial (pos k) (pos (S k'))) v w x : 
  dp_eval (vec_pos (x ## v)) (vec_pos w) (dio_move P) =
  dp_eval (vec_pos v) (vec_pos (x ## w)) P.
Proof.
  induction P as [n | n | p | op P1 IH1 P2 IH2].
  - reflexivity.
  - reflexivity.
  - unfold dio_move. eapply (Fin.caseS' p); reflexivity.
  - cbn -[vec_pos]; destruct op; congruence.
Qed.

Theorem Diophantine_to_MuRec_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  functional R ->
  Diophantine' R -> MuRec_computable R.
Proof.
  intros HR (k' & P1 & P2 & H).
  eapply (MuRec_computable_functional_iff _ HR).
  unshelve eexists.
  - eapply ra_comp. 1:  refine (ra_project (Fin.F1)).
    2: exact (ra_dio_poly_find (dio_move P1) (dio_move P2) ## vec_nil).
    exact k'. 
  - split.
    + intros v m. specialize (H (Vector.cons _ m _ v)).
      cbn -[dp_eval Vector.nth] in H. rewrite H.
      rewrite <- ra_bs_correct, ra_rel_fix_comp. unfold s_comp.
      intros (vi & H1 & H2). revert H1 H2.
      eapply (Vector.caseS' vi). clear vi. intros im.
      refine (Vector.case0 _ _).
      intros Hproj Hfind. specialize (Hfind Fin.F1).
      
      cbn -[ra_dio_poly_find] in Hfind.
      eapply ra_dio_poly_find_spec_strong1 in Hfind.
      eapply ra_project_rel in Hproj. clear H. subst.
      pose (w := (recomp.project (S k') im)).
      exists (fun j => vec_pos w (Fin.FS j)).
      generalize (eq_refl w). unfold w at 1.
      eapply (Vector.caseS' w). clear w. intros x w Hw.
      rewrite Hw in Hfind. rewrite !dio_move_spec in Hfind.
      erewrite dp_eval_ext.
      * rewrite Hfind. eapply dp_eval_ext.
        -- intros. reflexivity.
        -- intros. rewrite vec_pos_spec. cbn [vec_pos vec_head]. rewrite Hw. reflexivity.
      * intros. reflexivity.
      * intros. cbn [vec_head]. rewrite Hw. unfold vec_pos at 1. cbn [pos_S_inv]. now rewrite vec_pos_spec.
   +  intros v m Hvm. specialize (H (Vector.cons _ m _ v)).
      cbn -[dp_eval Vector.nth] in H. eapply H in Hvm as [ν Hν].
      erewrite dp_eval_ext in Hν at 1.  1: symmetry in Hν.
      1: erewrite dp_eval_ext in Hν at 1.  1: symmetry in Hν.
      1: erewrite <- !dio_move_spec in Hν.
      1: eapply ra_dio_poly_find_spec_strong2 in Hν as [e Hν].
      1: eexists.
      1: rewrite <- ra_bs_correct, ra_rel_fix_comp.  1: unfold s_comp.
      1: eexists.  1: split.
      * eapply ra_project_rel. reflexivity.
      * intros p. eapply (Fin.caseS' p). 2: eapply Fin.case0.
        rewrite vec_pos_map. 
        instantiate (1 := e ## vec_nil). 
        cbn [vec_pos pos_S_inv]. 
        eassumption.
      * intros. instantiate (1 := vec_set_pos _). now rewrite vec_pos_set.
      * intros. now rewrite vec_pos_spec.
      * intros. now rewrite vec_pos_set.
      * intros. now rewrite vec_pos_spec. Unshelve. 
Qed. 