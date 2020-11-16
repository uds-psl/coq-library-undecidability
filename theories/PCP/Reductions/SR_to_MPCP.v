Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.

Require Import Undecidability.Synthetic.Definitions.

(** * SR to MPCP *)

Section SR_to_MPCP.
  Local Definition string := string nat.
  Variable R : stack nat.
  Variables x0 y0 : string.

  Notation "x ≻ y" := (rew R x y) (at level 70).
  Notation "x ≻* y" := (rewt R x y) (at level 70).

  Notation Sigma := (x0 ++ y0 ++ sym R).

  Definition dollar := fresh Sigma.
  Notation "$" := dollar.
  Definition hash := fresh (dollar :: Sigma).
  Notation "#" := hash.

  Lemma sep_doll : $ <> #.
  Proof.
    intros H. symmetry in H. now eapply fresh_spec in H.
  Qed.

  Lemma doll_sig a : a el Sigma -> $ <> a.
  Proof.
    now eapply fresh_spec.
  Qed.

  Lemma hash_sig a : a el Sigma -> # <> a.
  Proof.
    intros; eapply fresh_spec. eauto.
  Qed.
  
  Definition d := [$] / ($ :: x0 ++ [#]).
  Definition e := (y0 ++ [#;$]) / [$].
  Definition P := [d ; e] ++ R ++ [ ([#] / [#] )] ++ map (fun a => [a] / [a]) Sigma.

  Lemma P_inv c :
    c el P ->
    c = d \/ c = e \/ c el R \/ c = ( [#] / [#] ) \/ exists a, a el Sigma /\ c = [a] / [a].
  Proof.
    cbn. intros. firstorder. eapply in_app_iff in H. firstorder.
    eapply in_map_iff in H. firstorder.
  Qed.

  Lemma cards_subset x1 : x1 <<= Sigma -> cards x1 <<= P.
  Proof.
    induction x1.
    - firstorder.
    - intros. intros [] [].
      + inv H0.  unfold P. eauto 15.
      + eapply IHx1; firstorder.
  Qed.

  Lemma rew_subset u v : u / v el R -> u / v el P.
  Proof.
    unfold P. intros. eauto.
  Qed.
  
  Fact SR_MPCP x :
    x <<= Sigma -> x ≻* y0 -> exists A, A <<= P /\ tau1 A = x ++ [#] ++ tau2 A.
  Proof.
    intros. revert H. pattern x; refine (rewt_induct _ _ H0).
    - exists [e]. cbn. firstorder. now simpl_list.
    - clear x H0. intros. inv H. destruct H1 as (A & ? & ?).
      pose (app_incl_l H2). pose (app_incl_R (app_incl_R H2)).
      repeat eapply incl_app; try assumption. eauto.
      exists (cards x1 ++ [(u / v)] ++ cards y1 ++ [ [#] / [#] ] ++ A). split.
      + repeat (eapply incl_app); try assumption; unfold P.
        * eapply cards_subset. eapply app_incl_l. eassumption.
        * eapply incl_appr. eapply incl_appl. now apply ListAutomation.incl_sing.
        * eapply cards_subset. eapply app_incl_R. eapply app_incl_R. eassumption.
        * eauto.
      + simpl_list. cbn. rewrite H1. now simpl_list. 
  Qed.

  Fact MPCP_SR x y A :
    A <<= P -> x <<= Sigma -> y <<= Sigma -> 
    tau1 A = x ++ [#] ++ y ++ tau2 A ->
    y ++ x ≻* y0.
  Proof.
    intros ?. revert x y. induction A; intros.
    - exfalso. destruct x; inv H2.
    - assert (a el P) as [ -> | [ ->  | [ | [-> | (? & ? & ->)]]]]  % P_inv by (now apply H).
      + exfalso. cbn -[fresh] in H2. destruct x. inv H2. destruct (sep_doll H4).
        inversion H2. edestruct doll_sig; eauto.
      + cbn -[fresh] in *.
        autorewrite with list in *. cbn -[fresh] in *.
        eapply list_prefix_inv in H2 as [<- ?].
        destruct y.
        * reflexivity.
        * exfalso. inversion H2. edestruct doll_sig; eauto. 
        * intros E. edestruct hash_sig; eauto.
        * intros E. edestruct hash_sig; eauto.
      + destruct a as (u, v).
        cbn -[fresh] in H2.
        edestruct (split_inv H2) as (x' & ->).
        intros E. edestruct hash_sig. unfold Sigma. rewrite !in_app_iff. do 2 right. now eapply sym_word_l; eauto. reflexivity.
        econstructor. eapply rewB. now eassumption.        
        enough ( (y ++ v) ++ x' ≻* y0) by now autorewrite with list in *.
        eapply IHA; autorewrite with list in *.
        * eauto.
        * eapply app_incl_R. eassumption.
        * eapply incl_app; eauto.
        * now eapply app_inv_head in H2.
      + cbn -[fresh] in H2. destruct x; [inv H2 |].
        * simpl_list. change y with ([] ++ y). eapply IHA; eauto using cons_incl.
        * inversion H2. edestruct hash_sig; eauto.       
      + cbn -[fresh] in *. rename x1 into a. destruct x.
        * inversion H2. edestruct hash_sig; eauto.
        * inv H2.
          replace (y ++ n :: x) with ((y ++ [n]) ++ x) by now simpl_list.
          eapply IHA. 
          ** eapply cons_incl. eassumption.
          ** eapply cons_incl. eassumption.
          ** eapply incl_app. eassumption. now eapply ListAutomation.incl_sing.
          ** simpl_list. eassumption.
  Qed.

  Corollary SR_MPCP_cor :
    x0 ≻* y0 <-> exists A, A <<= P /\ tau1 (d :: A) = tau2 (d :: A).
  Proof.
    split.
    - intros ?. cbn in H. eapply SR_MPCP in H as (A & ? & ?).
      exists A. firstorder. cbn. rewrite H0. cbn. now simpl_list.
      eapply incl_appl. apply incl_refl.
    - intros (A & ? & ?). eapply MPCP_SR with (y := []) (A := A); try trivial.
      eapply incl_appl. now apply incl_refl.
      inv H0. rewrite H2. now simpl_list.
  Qed.
      
End SR_to_MPCP.

Theorem reduction :
  SR ⪯ MPCP.
Proof.
  exists (fun '(R, x, y) => (d R x y, P R x y)). intros [[R x] y].
  unfold SR. rewrite SR_MPCP_cor. unfold MPCP. unfold d.
  firstorder trivial.
Qed.
