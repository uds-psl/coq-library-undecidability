From Undecidability.MinskyMachines Require Import MM_computable MM_sss mm_utils.
From Undecidability.StackMachines Require Import BSM_computable.

From Undecidability.Shared.Libs.DLW Require Import vec pos sss subcode.

Require Import Lia Vector Nat Arith List.

From Undecidability.MinskyMachines.MM
  Require Import mm_defs mm_utils mm_comp_strong. 

Definition MM_cast {n} (P : list (mm_instr (Fin.t n))) {m} (E : n = m) : list (mm_instr (Fin.t m)).
subst m. exact P. Defined.

Lemma MM_cast_length {n} (P : list (mm_instr (Fin.t n))) {m} (E : n = m) :
  length (MM_cast P E) = length P.
Proof.
  destruct E. cbn. reflexivity.
Qed.

Lemma cast_eq_refl {X n} (v : Vector.t X n) E : cast v E = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma fin_cast_eq_refl {n} (v : pos n) E : Fin.cast v E = v.
Proof.
  induction v; cbn; congruence.
Qed.


Lemma MM_cast_spec {n m} i (P : list (mm_instr (pos n))) (E : n = m) j v k w :
   sss.sss_output (@mm_sss _) (i, P) (j, v) (k, w) <-> sss.sss_output (@mm_sss _) (i, MM_cast P E) (j, Vector.cast v E) (k, Vector.cast w E).
Proof.
  destruct E. cbn. now rewrite !cast_eq_refl.
Qed.

Local Notation "P '/MM/' s '~~>' t" := (sss.sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s '~~>' t" := (sss.sss_output (@mm_sss _) P s t) (at level 70, no associativity).


Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Lemma vec_app_spec {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_app v w = Vector.append v w.
Proof.
  induction v.
  - cbn. eapply vec_pos_ext. intros. now rewrite vec_pos_set.
  - rewrite vec_app_cons. cbn. congruence.
Qed.


Lemma vec_change_swap [X] [n] (v : vec X n) (p : pos n) (q : pos n) x y :
p <> q ->
v[x / p][y / q] = v [y / q][x / p].
Proof.
  intros Hnew. eapply vec_pos_ext. intros r.
  destruct (pos_eq_dec q r).
  - subst. rewrite vec_change_eq, vec_change_neq, vec_change_eq; congruence.
  - destruct (pos_eq_dec p r).
    + subst. rewrite vec_change_neq, vec_change_eq, vec_change_eq; congruence.
    + rewrite !vec_change_neq; congruence.
Qed.

Lemma pos_left_inj {n m} p q :
  @pos_left n m p = @pos_left n m q -> p = q.
Proof.
  induction p in q |- *; cbn in *. 
  - eapply (Fin.caseS' q).
    + reflexivity.
    + clear q. cbn. congruence.
  - eapply (Fin.caseS' q).
    + cbn. congruence.
    + clear q. cbn. intros. f_equal. eapply IHp.
      now eapply pos_nxt_inj.
Qed.

Lemma pos_right_inj {n m} p q :
  @pos_right n m p = @pos_right n m q -> p = q.
Proof.
  induction n in p, q |- *; cbn in *. 
  - eauto.
  - intros. eapply IHn, pos_nxt_inj, H.
Qed.

Lemma pos_right_left {n m} p q :
  @pos_left n m p <> @pos_right n m q.
Proof.
  induction n; cbn.
  - inversion p.
  - eapply (Fin.caseS' p).
    + cbn. congruence.
    + cbn. intros ? ? % pos_nxt_inj. firstorder.
Qed.

Lemma cast_vec_pos { X n m} (v : Vector.t X n) (E : n = m) p :
  cast v E #> p = v #> Fin.cast p (eq_sym E).
Proof.
  destruct E. cbn. now rewrite cast_eq_refl, fin_cast_eq_refl.
Qed.

Lemma cast_ext { X n m} (v1 v2 : Vector.t X n) (E1 E2 : n = m) :
  v1 = v2 ->
  cast v1 E1 = cast v2 E2.
Proof.
  intros ->.
  destruct E1. cbn. now rewrite !cast_eq_refl.
Qed.

Lemma nth_error_vec_list {X n} (v : Vector.t X n) m (H : m < n) x :
  nth_error (vec_list v) m = Some x ->
  v #> Fin.of_nat_lt H = x.
Proof.
  induction v in m , H |- *; cbn.
  - lia.
  - destruct m; cbn.
    + congruence.
    + eapply IHv.
Qed.

Lemma vec_list_inj {X n} (v w : Vector.t X n) :
  vec_list v = vec_list w -> v = w.
Proof.
  induction v in w |- *.
  - pattern w. revert w. eapply Vector.case0. reflexivity.
  - eapply (Vector.caseS' w). clear w. intros y w. cbn.
    intros [= ->]. f_equal. eauto.
Qed.

Lemma vec_list_vec_app {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_list (vec_app v w) = vec_list v ++ vec_list w.
Proof.
  rewrite ! vec_app_spec.
  induction v in w |- *.
  - cbn. reflexivity.
  - cbn. f_equal. eauto.
Qed.

Fixpoint update {X} (n : nat) (l : list X) y :=
  match l, n with
  | nil, _ => nil
  | x :: l, 0 => y :: l
  | x :: l, S n => x :: update n l y
  end.

Lemma vec_list_vec_change {X n} (v : Vector.t X n) (x : X) (p : pos n) :
  vec_list (vec_change v p x) = update (proj1_sig (Fin.to_nat p)) (vec_list v) x.
Proof.
  induction v; cbn.
  - inversion p.
  - eapply (Fin.caseS' p); cbn.
    + cbn. reflexivity. 
    + intros. specialize (IHv p0). destruct (Fin.to_nat p0) eqn:E. cbn in *. now f_equal.
Qed.

Lemma vec_list_cast {X n} (v :Vector.t X n) m (E : n = m) :
 vec_list (cast v E) = vec_list v.
Proof.
  destruct E. now rewrite cast_eq_refl.
Qed.

Lemma vector_inv_back {X n} (v : Vector.t X (S n)) E :
  { '(x, v') : X * Vector.t X n | v = Vector.cast (append v' (x ## vec_nil)) E }.
Proof.
Admitted.

Lemma pos_left_spec {m n} p :
  @pos_left m n p = Fin.L n p.
Proof.
  induction p; cbn; congruence.
Qed.

Lemma pos_right_spec {m n} p :
  @pos_right m n p = Fin.R m p.
Proof.
  induction m; cbn; congruence.
Qed.

Lemma update_app_right {X} (x : X) l1 l2 i : 
  i >= length l1 ->
  update i (l1 ++ l2) x = l1 ++ update (i - length l1) l2 x.
Proof.
  induction l1 in i |- *; cbn.
  - now rewrite Nat.sub_0_r.
  - intros Hi. destruct i. lia.
    cbn. rewrite IHl1. reflexivity. lia.
Qed.

Lemma update_app_left {X} (x : X) l1 l2 i : 
  i < length l1 ->
  update i (l1 ++ l2) x = update i l1 x ++ l2.
Proof.
  induction l1 in i |- *; cbn.
  - lia. 
  - intros Hi. destruct i; cbn.
    + reflexivity.
    + rewrite IHl1. reflexivity. lia.
Qed.

Section preprocess.

  Variables k n : nat.

  Notation reg p := (@pos_left (1 + k + n) 2 (pos_left n (pos_right 1 p))).
  Notation tmp p := (@pos_right (1 + k + n) 2 p).

  Lemma tmp0_tmp1 : tmp pos0 <> tmp pos1. Proof. intros H % pos_right_inj. congruence. Qed.

  Lemma tmp_tgt p : tmp p <> pos0. Proof. cbn. congruence. Qed.

  Lemma tmp_reg p q : tmp p <> reg q. Proof. cbn. intros H % pos_nxt_inj. eapply pos_right_left. now rewrite H. Qed.

  Lemma tgt_reg p : reg p <> pos0. Proof. cbn. congruence. Qed.

  Lemma reg_inj p q : reg p = reg q -> p = q. Proof. cbn. now intros ? % pos_nxt_inj % pos_left_inj % pos_left_inj. Qed.

  Hint Resolve tmp0_tmp1 tmp_tgt tmp_reg tgt_reg reg_inj : core.

  Section prep.

  Import ListNotations.

  Definition prep (p : pos k) (i : nat) : list (mm_instr (pos (1 + k + n + 2))) := 
  (* i: *)    mm_transfert (reg p) pos0 (tmp pos0) i ++
  (* i+3: *) [INC (reg p)] ++
  (* i+4: *) [DEC Fin.F1 (14 + i)] ++ 
  (* i+5 *)   mm_push_One (reg p) (tmp pos0) (tmp pos1) (5+i) ++
  (* i+13: *)[DEC (tmp pos0) (4 + i) ].    

  End prep.

  Lemma prep_length p i : length (prep p i) = 14. Proof. reflexivity. Qed.

  Lemma prep_spec (p : pos k) v i np :
    v #> pos0 = 0 ->
    v #> tmp pos0 = 0 ->
    v #> tmp pos1 = 0 ->
    v #> reg p = np ->
    (i, prep p i) /MM/ (i, v) ~~> (14 + i, v [ (stack_enc (List.repeat true (v #> reg p))) / reg p]).
  Proof.
    intros Htgt Htmp1 Htmp2 Hnp. unfold prep.
    split. 2:{ cbn. lia. }
    eapply sss_compute_trans.
    { eapply subcode_sss_compute with (P := (i,mm_transfert (reg p) (pos0) (pos_right (1 + k + n) Fin.F1) i)). auto.
      eapply sss_progress_compute. eapply mm_transfert_progress; auto. }
    mm sss INC with (pos_left 2 (pos_left n (pos_right 1 p))). replace (3 + i) with (i + 3) by lia. auto.
    rew vec. replace (1 + (3 + i)) with (4 + i) by lia.
    rewrite vec_change_swap.
    rewrite vec_change_idem. 
    pose (npm := 0).
    match goal with [ |- context [vec_change ?v ?x 1]] => change (vec_change v x 1) with (vec_change v x (stack_enc (repeat true npm))) end.
    assert (np = np + npm) by lia.
    rewrite Hnp. revert Hnp. revert H. 2:auto.
    generalize np at 2 4. generalize npm. intros npr npl Heq Hnp.
    induction npl in npr, np, Heq, Hnp |- *.
    - eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (i+4, DEC Fin.F1 (14 + i) :: List.nil)). auto.
        mm sss DEC 0 with pos0 (14 + i). replace (4 + i) with (i + 4) by lia. eapply subcode_refl. rew vec. fold plus.
        mm sss stop. }
      mm sss stop. f_equal. cbn.
      rewrite vec_change_swap. 2:congruence.
      match goal with [ |- context [@vec_change ?X ?n ?vv ?x 0]] => replace (@vec_change X n vv x 0) with (vec_change vv x (v#>pos0)) end.
      2: now rewrite Htgt. rewrite vec_change_same. subst. reflexivity.
    - eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (i+4, DEC Fin.F1 (14 + i) :: List.nil)). auto.
        mm sss DEC S with pos0 (14 + i) npl. replace (4 + i) with (i + 4) by lia. eapply subcode_refl. rew vec. fold plus.
        mm sss stop. }
      rew vec.
      eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (5 + i, mm_push_One (pos_left 2 (pos_left n (pos_right 1 p))) (pos_right (1 + k + n) pos0) (pos_right (1 + k + n) pos1) (5+i))).
        1: replace (5 + i) with (i + 5) at 1 by lia; auto.
        eapply sss_progress_compute. eapply mm_push_One_progress; rew vec.
        - rewrite vec_change_neq; eauto.
        - rewrite vec_change_neq; eauto. }
      mm sss DEC 0 with (pos_right (1 + k + n) Fin.F1) (4 + i).
      replace (8 + (1 + (4 + i))) with (i + 13) by lia. auto.
      rewrite vec_change_neq. 2:auto. rewrite vec_change_neq. 2:auto.
      rewrite vec_change_neq. 2:auto. eauto.
      rewrite vec_change_swap. 2:auto. rewrite vec_change_idem.
      change (true :: repeat true npr) with (repeat true (S npr)). eapply IHnpl.
      lia. assumption.
  Qed.

  Fixpoint PREP' (k' : nat) (H : k' <= k) (i : nat) : list (mm_instr (pos (1 + k + n + 2))).
  Proof.
    destruct k'.
    - exact List.nil.
    - refine (List.app (PREP' k' _ i) _). abstract lia.
      assert (Hn : k' < k) by abstract lia.
      refine (prep (Fin.of_nat_lt Hn) (14 * k' + i)).
  Defined. 

  Lemma PREP'_length k' H i : length (@PREP' k' H i) = k' * 14.
  Proof.
    induction k' in i, H |- *; cbn.
    - reflexivity.
    - autorewrite with list. rewrite IHk'. cbn. lia.
  Qed.

  Definition PREP (i : nat) : list (mm_instr (pos (1 + k + n + 2))). refine (@PREP' k _ i). abstract lia. Defined.

  Lemma PREP_length i : length (PREP i) = k * 14. Proof. eapply PREP'_length. Qed.
  Hint Resolve PREP_length : core.    

  Lemma PREP_spec_strong i x w k'' k' v1 v2 v :
    forall E : k'' + k' = k,
    v = (Vector.cast (Vector.append v1 v2) E) ->
    x = 0 ->
    forall H,
    (i, PREP' k'' H i) /MM/ (i, Vector.append (Vector.append (x ## v) w) (0 ## 0 ## vec_nil)) ~~>
    (i + (k'' * 14), Vector.append (Vector.append (x ## (Vector.cast (Vector.append (Vector.map (fun n => stack_enc (List.repeat true n)) v1) v2) E)) w) (0 ## 0 ## vec_nil)).
  Proof. 
    intros E -> -> Hle. 
    split. 2:{ cbn. rewrite PREP'_length. right. lia. }
    revert i v1 k' Hle E v2.
    induction k'' as [ | k'' ]; intros i v1 k' Hle E v2.
    - cbn. mm sss stop. f_equal. lia. revert v1. eapply Vector.case0. cbn. reflexivity.
    - cbn [PREP'].
      edestruct (vector_inv_back v1) as [(x, v1l) Hv1].
      assert (H1 : k'' <= k) by lia.
      assert (H2 : k'' + S k' = k) by lia.
      specialize (IHk'' i v1l (S k') (PREP'_subproof k'' Hle) H2 (x ## v2)).
      eapply subcode_sss_compute_trans with (P := (i, PREP' k'' (PREP'_subproof k'' Hle) i)). auto.
      match type of IHk'' with sss_compute _ _ (_, ?st) _ => evar (Vector.t nat (1 + k + n + 2)); enough (Eq : st = t) end; subst t.
      rewrite Eq in IHk''. eapply IHk''.
      { rewrite Hv1. repeat f_equal.
        eapply vec_list_inj. rewrite !vec_list_cast, <- !vec_app_spec, !vec_list_vec_app.
        rewrite vec_list_cast. rewrite vec_list_vec_app. cbn. now rewrite <- app_assoc.
      }
      replace (14 * k'' + i) with (i + k'' * 14) by lia.
      eapply subcode_sss_compute_trans with (P := (i + k'' * 14, prep (Fin.of_nat_lt (PREP'_subproof0 k'' Hle)) (i + k'' * 14))).
      { eexists. eexists. split. reflexivity. rewrite PREP'_length. lia. }
      eapply prep_spec.
      + reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite vec_pos_app_right. reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite vec_pos_app_right. reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite !vec_pos_app_left. reflexivity.
      + mm sss stop. f_equal. 1:lia.
        rewrite <- !vec_app_spec.
        eapply vec_list_inj.
        
        rewrite vec_list_vec_change.
        rewrite !(@vec_list_vec_app nat (1 + k + n) 2).
        rewrite !vec_list_vec_app. cbn [vec_list].
        rewrite !vec_list_cast.
        rewrite !vec_list_vec_app. cbn [vec_list].
        rewrite !vec_list_vec_map. rewrite Hv1. rewrite vec_list_cast.
        rewrite <- !vec_app_spec.
        rewrite !vec_list_vec_app. cbn [vec_list].
        clear. fold plus.
        rewrite pos_left_spec. pose proof (@Fin.L_sanity (S (k + n)) 2). cbn in H. rewrite H. clear H.
        rewrite pos_left_spec. pose proof (@Fin.L_sanity (S (k)) n). cbn in H. rewrite H. clear H.
        rewrite pos_right_spec. pose proof (@Fin.R_sanity k 1 ). cbn [plus] in H. rewrite H. clear H.
        rewrite Fin.to_nat_of_nat. cbn [proj1_sig update app]. f_equal.
        rewrite map_app. cbn [map].
        rewrite <- !pos_left_spec.
        rewrite update_app_left. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        rewrite update_app_left. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        rewrite update_app_right. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        simpl_list. rewrite vec_list_length. rewrite minus_diag. cbn [update].
        f_equal. f_equal.
        rewrite <- !app_assoc. f_equal.
        cbn [app]. f_equal. f_equal. f_equal.
        rewrite (@vec_pos_app_left nat (add (S k) n) 2).
        rewrite <- pos_left_spec.
        rewrite (@vec_pos_app_left nat (S k) n).
        rewrite <- pos_right_spec.
        cbn [pos_right]. cbn.
        eapply nth_error_vec_list.
        rewrite vec_list_cast, !vec_list_vec_app.
        rewrite nth_error_app2; rewrite vec_list_length. 2: lia.
        rewrite minus_diag. reflexivity.
        Unshelve. lia.
  Qed.

  Lemma myeq m : m + 0 = m.
  Proof.
    induction m.
    - reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Defined.

  Lemma PREP_spec i v w :
      (i, PREP i) /MM/ (i, Vector.append (Vector.append (0 ## v) w) (0 ## 0 ## vec_nil)) ~~> (i + (k * 14), Vector.append (Vector.append (0 ## Vector.map (fun n => stack_enc (List.repeat true n)) v) w) (0 ## 0 ## vec_nil)).
  Proof.
    unfold PREP.
    pose proof (@PREP_spec_strong i 0 w k 0 v vec_nil v (myeq k)).
    match goal with [ |- sss_output _ _ (_, ?st) _ ] => evar (Vector.t nat (1 + k + n + 2)); enough (st = t) as ->; subst t end.
    match goal with [ |- sss_output _ _ _ (_, ?st) ] => evar (Vector.t nat (1 + k + n + 2)); enough (st = t) as ->; subst t end.
    eapply H; try reflexivity. 3: reflexivity.
    2:{ repeat f_equal. clear. induction k; cbn. 
        - rewrite cast_eq_refl.
          pattern v. revert v. eapply Vector.case0. reflexivity.
        - eapply (Vector.caseS' v). clear v. intros x v. cbn.
        f_equal. rewrite IHn. eapply cast_ext. f_equal. eapply IHn.
    }
    clear. generalize (myeq k).
    induction v; intros E.
    - cbn. reflexivity.
    - cbn. f_equal. eapply IHv.
  Qed.

  Definition POSTP (i : nat) : list (mm_instr (pos (1 + k + n + 2))) := @List.nil _.

  Lemma POSTP_spec i v out :
     v #> pos_right (1 + k + n) Fin.F1 = 0 ->
     v #> Fin.F1 = stack_enc (List.repeat true out) ->
     (i, POSTP i) /MM/ (i, v) ~~> (i + 3, v [ out / Fin.F1 ]).
  Admitted.

End preprocess.

Lemma cast_cast {n m} {E : n = m} {X} (v : Vector.t X n) (E2 : m = n) :
  cast (cast v E) E2 = v.
Proof.
  destruct E. now rewrite !cast_eq_refl.
Qed.

Definition cases {k i} : (forall p : pos (1 + k + i + 2),
{p = pos_right (1 + k + i) pos0} + {p = pos_right (1 + k + i) pos1} +
{q : pos (1 + k + i) | p = pos_left 2 q}).
Proof.
  apply pos_left_right_rect; [ eauto | ].
  intros p. eapply (Fin.caseS' p); [ eauto | ].
  intros p'. eapply (Fin.caseS' p'); [ eauto | ].
  eapply Fin.case0.
Defined.

Lemma MM_computable_to_BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  BSM_computable R -> MM_computable R.
Proof.
  intros (i & n & P & HP). red.
  unshelve epose proof (@bsm_mm_compiler_strong (1 + k + i) n P (pos_right _ Fin.F1) (pos_right _ (Fin.FS Fin.F1)) (pos_left _) (1 + length (PREP k i 1)) _ _ _ _ ) as [Q HQ]. 
  - eapply tmp0_tmp1.
  - intros p. intros H. eapply  pos_right_left. now rewrite H.
  - intros.  intros H. eapply  pos_right_left. now rewrite H.
  - now intros ? ? ? % pos_left_inj.
  - exact cases.
  - exists (i + 2). assert (E : 1 + k + i + 2 = (1 + k) + (i + 2)) by lia.
    pose (q' := (List.app (List.app (PREP k i 1) Q) (POSTP k i 20))).
    exists (MM_cast q' E). fold plus.
    intros v m. etransitivity. 
    { split. intros ? % HP. exact H0. eapply HP. }
    assert (Eq1 : cast (append (append (0 ## v) (const 0 i)) (const 0 2)) E = append (0 ## v) (const 0 (i + 2))).
    { clear. cbn.
      f_equal. match goal with [ |- context [@f_equal ?A ?B ?f ?x ?y ?e]] => generalize (@f_equal A B f x y e) end. clear.
      induction v; cbn; intros E.
      - induction i in E |- *; cbn.
        + reflexivity.
        + now rewrite IHi.
      - f_equal. now rewrite IHv.
    }
    setoid_rewrite eval_iff. split.
    + intros (c & v' & H % BSM_sss.eval_iff). fold plus in *.
      eapply HQ in H. 
      eexists. eexists ?[v']. rewrite <- Eq1.
      unshelve eassert (Eq2 : forall v' : Vector.t nat (k + (i + 2)), m ## v' = cast (m ## _) E).
      { fold plus. refine (Vector.cast v' _). abstract lia. }
      { clear. intros v. cbn. f_equal.
        match goal with [ |- context [@f_equal ?A ?B ?f ?x ?y ?e]] => generalize (@f_equal A B f x y e) end. fold plus.
        intros E2. generalize (MM_computable_to_BSM_computable_subproof k i E).
        clear. intros E1. cbn in *. revert v E1 E2. generalize (k + i + 2).  generalize (k + (i + 2)). clear. intros.
        destruct E1. now rewrite !cast_eq_refl.
      }
      rewrite Eq2.
      instantiate (v' := (cast _ _)).
      rewrite <- @MM_cast_spec. subst q'.
      split. 
      1: { eapply subcode_sss_compute_trans. 2: eapply PREP_spec. 1: auto.
      match goal with [H : sss_output _  _ ?st1 _ |- sss_compute _ _ ?st2 _ ] => assert (st1 = st2) by admit end.
      rewrite H0 in H.
      eapply subcode_sss_compute_trans. 2: eapply H. auto.
      unfold vec_enc. unfold vec_set_pos. cbn [plus].
      destruct cases as [ [ | ] | [q Hq]]. 
      1:{ cbn in *. congruence.  }
      1:{ cbn in *; congruence. }
      revert Hq. eapply (Fin.caseS' q).
      2:{ cbn. congruence. }
      intros _. clear q.
      eapply subcode_sss_compute_trans. 2: eapply POSTP_spec. admit.
      { cbn. rewrite vec_pos_set. destruct cases as [ [ | ] | [q Hq]]. 
      1:{ cbn in *. congruence.  }
      1:{ cbn in *; congruence. }
      revert Hq. eapply (Fin.caseS' q).
      2:{ cbn. intros ? ? % pos_nxt_inj. exfalso. eapply pos_right_left. now rewrite H1. }
      clear H. cbn. congruence.
      }
      { cbn. reflexivity. }
      mm sss stop. cbn. f_equal.
      rewrite cast_cast.
      reflexivity.
      }
      cbn. autorewrite with list. setoid_rewrite PREP_length. lia.
Qed.
