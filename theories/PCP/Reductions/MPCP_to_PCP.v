Require Import Bool List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Import PCPListNotation.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.Definitions.

Local Hint Rewrite <- app_assoc : list.
Local Hint Resolve in_eq in_nil in_cons in_or_app : core.

Set Default Goal Selector "!".

(* * MPCP to PCP *)
Section MPCP_PCP.
  Local Definition card := card nat.
  Local Definition string := string nat.
  Local Notation "x / y" := (x, y).
  Variable R : list (card).
  Variable x0 y0 : string.

  Definition Sigma := sym (x0/y0 :: R).
  Definition R_Sigma : sym R <<= Sigma.
  Proof. unfold Sigma. cbn. do 2 apply incl_appr. apply incl_refl. Qed.

  Definition dollar := fresh Sigma.
  Notation "$" := dollar.
  Definition hash := fresh (dollar :: Sigma).
  Notation "#" := hash.

  Fixpoint hash_l (x : string) :=
    match x with
    | [] => []
    | a :: x => # :: a :: hash_l x
    end.
  Notation "#_L" := hash_l.

  Fixpoint hash_r (x : string) :=
    match x with
    | [] => []
    | a :: x => a :: # :: hash_r x
    end.
  Notation "#_R" := hash_r.

  Definition d := ($ :: (#_L x0)) / ($ :: # :: (#_R y0)).
  Definition e := [#;$] / [$].
  Definition P := [d;e] ++ map (fun '(x,y) => (#_L x, #_R y)) (filter (fun '(x,y) => is_cons x || is_cons y) (x0/y0::R)).

  Lemma P_inv c :
    c el P ->
    c = d \/ c = e \/ (exists x y, (x,y) el (x0/y0 :: R) /\ c = (#_L x, #_R y)  /\ ( (x,y) <> (nil, nil))).
  Proof.
    cbn -[filter]. intros. firstorder. eapply in_map_iff in H as ((x,y) & <- & (? & ? % orb_prop) % filter_In).
    rewrite !is_cons_true_iff in H0.
    right. right. exists x, y. firstorder; destruct x, y; cbn; firstorder congruence.
  Qed.

  Lemma P_inv_top x y a :
    a el Sigma ->
    ~(a :: x,y) el P.
  Proof.
    intros ? [  | [   | (x'' & y' & ? & ? & ?) ] ] % P_inv.
    - inv H0. edestruct fresh_spec; eauto.
    - inv H0. edestruct fresh_spec with (l := dollar :: Sigma); [ | reflexivity]. firstorder.
    - inv H1. destruct x''; cbn -[fresh] in *; [congruence | ]. inversion H4.
      edestruct fresh_spec with (l := dollar :: Sigma); [ | reflexivity ]. unfold hash in *.
      rewrite <- H3. firstorder.
  Qed.

  Lemma P_inv_bot x y :
    ~(y, # :: x) el P.
  Proof.
    intros [  | [  | (x'' & y' & ? & ? & ?) ] ] % P_inv.
    - inv H. edestruct fresh_spec; eauto.
    - inv H. edestruct fresh_spec; eauto.
    - inv H0. destruct y'; cbn -[fresh] in *; [congruence | ]. inversion H4.
      edestruct fresh_spec with (l := dollar :: Sigma); [ | reflexivity ]. unfold hash in *.
      rewrite H2. right. eapply sym_word_R; eauto.
  Qed.
  
  Lemma match_start d' B :
    d' :: B <<= P -> tau1 (d' :: B) = tau2 (d' :: B) -> d' = d.
  Proof.
    intros Hs Hm.
    assert (d' el P) as [ -> | [ ->  | (x & y & ? & -> & ?) ] ] % P_inv by now eapply Hs; cbn -[fresh] in Hm.
    - congruence.
    - inv Hm. now edestruct fresh_spec; eauto.
    - cbn in Hm. destruct x, y; try firstorder congruence.
      + destruct (tau1_inv Hm) as (x' & y' & ? ).
        pose (cons_incl Hs).
        assert ( (n :: x') / y' el P) as [] % P_inv_top by eauto.
        eapply sym_word_R; eauto.
      + cbn -[fresh] in Hm. symmetry in Hm. destruct (tau2_inv Hm) as (x' & y' & ? ).
        pose (cons_incl Hs).
        assert ( y' / (# :: x') el P) as [] % P_inv_bot by eauto.
      + cbn -[fresh] in Hm. inversion Hm. assert (fresh (dollar :: Sigma) = hash) by reflexivity. 
        edestruct fresh_spec; try eassumption. right.
        eapply sym_word_R in H. subst. eauto.
  Qed.

  Lemma hash_swap x :
    #_L x ++ [#] = # :: #_R x.
  Proof.
    induction x; cbn in *; now try rewrite IHx.
  Qed.

  Lemma hash_L_app x y :
    #_L (x ++ y) = #_L x ++ #_L y.
  Proof.
    induction x; cbn in *; now try rewrite IHx.
  Qed.

  Lemma hash_R_app x y :
    #_R (x ++ y) = #_R x ++ #_R y.
  Proof.
    induction x; cbn in *; now try rewrite IHx.
  Qed.

  Lemma hash_L_diff x y :
    #_L x <> # :: #_R  y.
  Proof.
    revert y. induction x; cbn -[fresh]; intros ? ?; inv H.
    destruct y; inv H1. firstorder.
  Qed.

  Lemma hash_R_inv x y :
    #_R x = #_R y -> x = y.
  Proof.
    revert y; induction x; intros [] H; inv H; firstorder congruence.
  Qed.
  
  Lemma doll_hash_L x:
    x <<= Sigma -> ~ $ el #_L x.
  Proof.
    induction x; intros.
    -- firstorder.
    -- intros [ | []].
       ++ now eapply fresh_spec in H0 as []. 
       ++ symmetry in H0. eapply fresh_spec in H0 as []. firstorder.
       ++ firstorder.
  Qed.

  Lemma MPCP_PCP x y A :
    A <<= x0/y0 :: R -> x ++ tau1 A = y ++ tau2 A ->
    exists B, B <<= P /\ (#_L x) ++ tau1 B = # :: #_R y ++ tau2 B.
  Proof.
    revert x y; induction A; cbn -[fresh P] in *; intros.
    - rewrite !app_nil_r in H0. subst. exists [e]. firstorder.
      cbn -[fresh].
      enough ((#_L y ++ [#]) ++ [$] = # :: #_R y ++ [$]) by now autorewrite with list in *.
      now rewrite hash_swap.
    - destruct a as (x', y').
      assert ( (x ++ x') ++ tau1 A = (y ++ y') ++ tau2 A) by now simpl_list.
      eapply IHA in H1 as (B & ? & ?) ; [ | firstorder].
      rewrite hash_L_app, hash_R_app in H2.
      autorewrite with list in H2.
      destruct (is_cons x' || is_cons y') eqn:E.
      + exists ( (#_L x' / #_R y') :: B). split.
        * intros ? [ <- | ]; [ | eauto].
          unfold P. rewrite in_app_iff, in_map_iff. right. exists (x', y'). split; [easy|].
          eapply filter_In. eauto.
        * eassumption. 
      + exists B. rewrite orb_false_iff, <- !not_true_iff_false, !is_cons_true_iff in E. destruct E.
        destruct x', y'; firstorder congruence.
  Qed.

  Lemma PCP_MPCP x y B :
    B <<= P -> x <<= Sigma -> y <<= Sigma ->
    (#_L x) ++ tau1 B = # :: (#_R y) ++ tau2 B ->
    exists A, A <<= x0/y0::R /\ x ++ tau1 A = y ++ tau2 A.
  Proof.
    revert x y. induction B; cbn -[fresh P] in *; intros.
    - exfalso. rewrite !app_nil_r in H2. eapply hash_L_diff in H2 as [].
    - assert (a el P) as [ -> | [ ->  | (x' & y' & ? & -> & ?) ] ] % P_inv by intuition; cbn -[fresh P] in *.
      + exfalso. setoid_rewrite app_comm_cons in H2 at 2.
        eapply list_prefix_inv in H2 as [[] % hash_L_diff E2].
        * now eapply doll_hash_L.
        * rewrite <- hash_swap. rewrite in_app_iff. intros [ | [ | []]]. { eapply doll_hash_L; eauto. }
          now eapply fresh_spec in H3 as []. 
      + exists []. assert ((#_L x ++ [#]) ++ $ :: tau1 B = (# :: #_R y) ++ $ :: tau2 B) by now simpl_list.
        eapply list_prefix_inv in H3.
        { rewrite hash_swap in H3. inv H3.
          inv H4. eapply hash_R_inv in H6 as ->. firstorder. }
        * rewrite in_app_iff. intros [ | [ | []]]. { eapply doll_hash_L in H4; eauto. }
          now eapply fresh_spec in H4 as []. 
        * rewrite <- hash_swap. rewrite in_app_iff. intros [ | [ | []]]. { eapply doll_hash_L; eauto. }
          now eapply fresh_spec in H4 as []. 
      + assert ((#_L x ++ #_L x') ++ tau1 B = # :: (#_R y ++ #_R y') ++ tau2 B) by now simpl_list.
        rewrite <- hash_L_app, <- hash_R_app in H5. eapply IHB in H5 as (A & ? & ?).
        * exists (x' / y' :: A). intuition idtac; try inv H7; auto with datatypes;
          cbn; now autorewrite with list in *. 
        * eapply incl_cons_inv. eassumption.
        * eapply incl_app. { eauto. }
          intros ? ?. destruct H3. { inv H3. eauto. } eapply R_Sigma, sym_word_l; eauto.
        * eapply incl_app. { eauto. }
          intros ? ?. destruct H3. { inv H3. eauto. } eapply R_Sigma, sym_word_R; eauto.
  Qed.

  Lemma MPCP_PCP_cor :
    MPCP (x0/y0, R) <-> PCP P.
  Proof.
    split.
    - intros (A & Hi & (B & HiB & H) % MPCP_PCP).
      + exists (d :: B).
        firstorder try congruence. 
        cbn. f_equal. now rewrite H.
      + eassumption.
    - intros ([|d' B] & Hi & He & H); firstorder.
      pose proof H as -> % match_start; eauto.
      cbn -[fresh] in H. inv H.
      eapply PCP_MPCP in H1; cbn.
      + eassumption.
      + eapply cons_incl. eassumption.
      + apply incl_appl. apply incl_refl.
      + apply incl_appr. apply incl_appl. apply incl_refl.
  Qed.

End MPCP_PCP.

Theorem reduction :
  MPCP ⪯ PCP.
Proof.
  exists (fun '(x, y, R) => P R x y).
  intros ((x & y) & R).
  eapply MPCP_PCP_cor.
Qed.
