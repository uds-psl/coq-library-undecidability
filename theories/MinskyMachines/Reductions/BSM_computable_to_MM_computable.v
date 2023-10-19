Set Default Goal Selector "!".

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

Lemma MM_cast_terminates {n m} i (P : list (mm_instr (pos n))) (E : n = m) j v :
   sss.sss_terminates (@mm_sss _) (i, P) (j, v) <-> sss.sss_terminates (@mm_sss _) (i, MM_cast P E) (j, Vector.cast v E).
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

Lemma vec_map_spec {X Y n} (v : Vector.t X n) (f : X -> Y) :
  vec_map f v = Vector.map f v.
Proof.
  induction v; cbn; congruence.
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
  destruct E. 
  destruct (splitat n v) eqn:E.
  eexists (vec_head t0, t).
  erewrite <- append_splitat. 1: now rewrite cast_eq_refl.
  rewrite E. f_equal. eapply (Vector.caseS' t0). cbn.
  intros h. eapply Vector.case0. reflexivity.
Qed.

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
  - intros Hi. destruct i. 1: lia.
    cbn. rewrite IHl1. 1: reflexivity. lia.
Qed.

Lemma update_app_left {X} (x : X) l1 l2 i : 
  i < length l1 ->
  update i (l1 ++ l2) x = update i l1 x ++ l2.
Proof.
  induction l1 in i |- *; cbn.
  - lia. 
  - intros Hi. destruct i; cbn.
    + reflexivity.
    + rewrite IHl1. 1: reflexivity. lia.
Qed.

Lemma vec_list_const {X x n} : vec_list (@const X x n) = List.repeat x n.
Proof. induction n; cbn; congruence. Qed.

Section preprocess.

  Variables k n : nat.

  Notation reg p := (@pos_left (1 + k + n) 3 (pos_left n (pos_right 1 p))).
  Notation tmp p := (@pos_right (1 + k + n) 3 p).

  Lemma tmp0_tmp1 : tmp pos0 <> tmp pos1. Proof. intros H % pos_right_inj. congruence. Qed.
  Lemma tmp0_tmp2 : tmp pos0 <> tmp pos2. Proof. intros H % pos_right_inj. congruence. Qed.
  Lemma tmp2_tmp0 : tmp pos2 <> tmp pos0. Proof. intros H % pos_right_inj. congruence. Qed.
  Lemma tmp1_tmp2 : tmp pos1 <> tmp pos2. Proof. intros H % pos_right_inj % pos_nxt_inj. congruence.  Qed.

  Lemma tmp_tgt p : tmp p <> pos0. Proof. cbn. congruence. Qed.

  Lemma tmp_reg p q : tmp p <> reg q. Proof. cbn. intros H % pos_nxt_inj. eapply pos_right_left. now rewrite H. Qed.

  Lemma tgt_reg p : reg p <> pos0. Proof. cbn. congruence. Qed.

  Lemma reg_inj p q : reg p = reg q -> p = q. Proof. cbn. now intros ? % pos_nxt_inj % pos_left_inj % pos_left_inj. Qed.

  Hint Resolve tmp0_tmp1 tmp0_tmp1 tmp2_tmp0 tmp1_tmp2 tmp_tgt tmp_reg tgt_reg reg_inj : core.

  Section prep.

  Import ListNotations.

  Definition prep (p : pos k) (i : nat) : list (mm_instr (pos (1 + k + n + 3))) := 
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
    { eapply subcode_sss_compute with (P := (i,mm_transfert (reg p) (pos0) (pos_right (1 + k + n) Fin.F1) i)). 1: auto.
      eapply sss_progress_compute. eapply mm_transfert_progress; auto. }
    mm sss INC with (pos_left 3 (pos_left n (pos_right 1 p))). 1: replace (3 + i) with (i + 3) by lia. 1: auto.
    rew vec. replace (1 + (3 + i)) with (4 + i) by lia.
    rewrite vec_change_swap.
    1: rewrite vec_change_idem. 
    1: pose (npm := 0).
    1: match goal with [ |- context [vec_change ?v ?x 1]] => change (vec_change v x 1) with (vec_change v x (stack_enc (repeat true npm))) end.
    1: assert (np = np + npm) by lia.
    1: rewrite Hnp. 1: revert Hnp. 1: revert H. 2:auto.
    generalize np at 2 4. generalize npm. intros npr npl Heq Hnp.
    induction npl in npr, np, Heq, Hnp |- *.
    - eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (i+4, DEC Fin.F1 (14 + i) :: List.nil)). 1: auto.
        mm sss DEC zero with pos0 (14 + i). 1: replace (4 + i) with (i + 4) by lia. 1: eapply subcode_refl. 1: rew vec. fold plus.
        mm sss stop. }
      mm sss stop. f_equal. cbn.
      rewrite vec_change_swap. 2:congruence.
      match goal with [ |- context [@vec_change ?X ?n ?vv ?x 0]] => replace (@vec_change X n vv x 0) with (vec_change vv x (v#>pos0)) end.
      2: now rewrite Htgt. rewrite vec_change_same. subst. reflexivity.
    - eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (i+4, DEC Fin.F1 (14 + i) :: List.nil)). 1: auto.
        mm sss DEC S with pos0 (14 + i) npl. 1:  replace (4 + i) with (i + 4) by lia. 1: eapply subcode_refl. 1:  rew vec. fold plus.
        mm sss stop. }
      rew vec.
      eapply sss_compute_trans.
      { eapply subcode_sss_compute with (P := (5 + i, mm_push_One (pos_left 3 (pos_left n (pos_right 1 p))) (pos_right (1 + k + n) pos0) (pos_right (1 + k + n) pos1) (5+i))).
        1: replace (5 + i) with (i + 5) at 1 by lia; auto.
        eapply sss_progress_compute. eapply mm_push_One_progress; rew vec.
        - rewrite vec_change_neq; eauto.
        - rewrite vec_change_neq; eauto. }
      mm sss DEC zero with (pos_right (1 + k + n) Fin.F1) (4 + i).
      1: replace (8 + (1 + (4 + i))) with (i + 13) by lia.  1: auto.
      1: rewrite vec_change_neq. 2:auto. 1:  rewrite vec_change_neq. 2:auto.
      1: rewrite vec_change_neq. 2:auto. 1:  eauto.
      rewrite vec_change_swap. 2:auto. rewrite vec_change_idem.
      change (true :: repeat true npr) with (repeat true (S npr)). eapply IHnpl.
      1: lia. assumption.
  Qed.

  Fixpoint PREP' (k' : nat) (H : k' <= k) (i : nat) : list (mm_instr (pos (1 + k + n + 3))).
  Proof.
    destruct k'.
    - exact List.nil.
    - refine (List.app (PREP' k' _ i) _).  1: abstract lia.
      assert (Hn : k' < k) by abstract lia.
      refine (prep (Fin.of_nat_lt Hn) (14 * k' + i)).
  Defined. 

  Lemma PREP'_length k' H i : length (@PREP' k' H i) = k' * 14.
  Proof.
    induction k' in i, H |- *; cbn.
    - reflexivity.
    - autorewrite with list. rewrite IHk'. cbn. lia.
  Qed.

  Definition PREP (i : nat) : list (mm_instr (pos (1 + k + n + 3))). refine (@PREP' k _ i). abstract lia. Defined.

  Lemma PREP_length i : length (PREP i) = k * 14. Proof. eapply PREP'_length. Qed.
  Hint Resolve PREP_length : core.    

  Lemma PREP_spec_strong i x w k'' k' v1 v2 v :
    forall E : k'' + k' = k,
    v = (Vector.cast (Vector.append v1 v2) E) ->
    x = 0 ->
    forall H,
    (i, PREP' k'' H i) /MM/ (i, Vector.append (Vector.append (x ## v) w) (0 ## 0 ## 0 ## vec_nil)) ~~>
    (i + (k'' * 14), Vector.append (Vector.append (x ## (Vector.cast (Vector.append (Vector.map (fun n => stack_enc (List.repeat true n)) v1) v2) E)) w) (0 ## 0 ## 0 ## vec_nil)).
  Proof. 
    intros E -> -> Hle. 
    split. 2:{ cbn. rewrite PREP'_length. right. lia. }
    revert i v1 k' Hle E v2.
    induction k'' as [ | k'' ]; intros i v1 k' Hle E v2.
    - cbn. mm sss stop. f_equal. 1:  lia. revert v1. eapply Vector.case0. cbn. reflexivity.
    - cbn [PREP'].
      edestruct (vector_inv_back v1) as [(x, v1l) Hv1].
      assert (H1 : k'' <= k) by lia.
      assert (H2 : k'' + S k' = k) by lia.
      specialize (IHk'' i v1l (S k') (PREP'_subproof k'' Hle) H2 (x ## v2)).
      eapply subcode_sss_compute_trans with (P := (i, PREP' k'' (PREP'_subproof k'' Hle) i)).  1: auto.
      1: match type of IHk'' with sss_compute _ _ (_, ?st) _ => evar (Vector.t nat (1 + k + n + 3)); enough (Eq : st = t) end; subst t.
      1: rewrite Eq in IHk''. 1:  eapply IHk''.
      { rewrite Hv1. repeat f_equal.
        eapply vec_list_inj. rewrite !vec_list_cast, <- !vec_app_spec, !vec_list_vec_app.
        rewrite vec_list_cast. rewrite vec_list_vec_app. cbn. now rewrite <- app_assoc.
      }
      replace (14 * k'' + i) with (i + k'' * 14) by lia.
      eapply subcode_sss_compute_trans with (P := (i + k'' * 14, prep (Fin.of_nat_lt (PREP'_subproof0 k'' Hle)) (i + k'' * 14))).
      { eexists. eexists. split.  1: reflexivity. rewrite PREP'_length. lia. }
      1: eapply prep_spec.
      + reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite vec_pos_app_right. reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite vec_pos_app_right. reflexivity.
      + cbn. rewrite <- !vec_app_spec. rewrite !vec_pos_app_left. reflexivity.
      + mm sss stop. f_equal. 1:lia.
        rewrite <- !vec_app_spec.
        eapply vec_list_inj.
        
        rewrite vec_list_vec_change.
        rewrite !(@vec_list_vec_app nat (1 + k + n) 3).
        rewrite !vec_list_vec_app. cbn [vec_list].
        rewrite !vec_list_cast.
        rewrite !vec_list_vec_app. cbn [vec_list].
        rewrite !vec_list_vec_map. rewrite Hv1. rewrite vec_list_cast.
        rewrite <- !vec_app_spec.
        rewrite !vec_list_vec_app. cbn [vec_list].
        clear. fold plus.
        rewrite pos_left_spec. pose proof (@Fin.L_sanity (S (k + n)) 3). cbn in H. rewrite H. clear H.
        rewrite pos_left_spec. pose proof (@Fin.L_sanity (S (k)) n). cbn in H. rewrite H. clear H.
        rewrite pos_right_spec. pose proof (@Fin.R_sanity k 1 ). cbn [plus] in H. rewrite H. clear H.
        rewrite Fin.to_nat_of_nat. cbn [proj1_sig update app]. f_equal.
        rewrite map_app. cbn [map].
        rewrite <- !pos_left_spec.
        rewrite update_app_left. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        rewrite update_app_left. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        rewrite update_app_right. 2:{ simpl_list. rewrite vec_list_length. cbn. lia. }
        simpl_list. rewrite vec_list_length. rewrite Nat.sub_diag. cbn [update].
        f_equal. f_equal.
        rewrite <- !app_assoc. f_equal.
        cbn [app]. f_equal. f_equal. f_equal.
        rewrite (@vec_pos_app_left nat (add (S k) n) 3).
        rewrite <- pos_left_spec.
        rewrite (@vec_pos_app_left nat (S k) n).
        rewrite <- pos_right_spec.
        cbn [pos_right]. cbn.
        eapply nth_error_vec_list.
        rewrite vec_list_cast, !vec_list_vec_app.
        rewrite nth_error_app2; rewrite vec_list_length. 2: lia.
        rewrite Nat.sub_diag. reflexivity.
        Unshelve. lia.
  Qed.

  Lemma myeq m : m + 0 = m.
  Proof.
    induction m.
    - reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Defined.

  Lemma PREP_spec i v w :
      (i, PREP i) /MM/ (i, Vector.append (Vector.append (0 ## v) w) (0 ## 0 ## 0 ## vec_nil)) ~~> (i + (k * 14), Vector.append (Vector.append (0 ## Vector.map (fun n => stack_enc (List.repeat true n)) v) w) (0 ## 0 ## 0 ## vec_nil)).
  Proof.
    unfold PREP.
    pose proof (@PREP_spec_strong i 0 w k 0 v vec_nil v (myeq k)).
    match goal with [ |- sss_output _ _ (_, ?st) _ ] => evar (Vector.t nat (1 + k + n + 3)); enough (st = t) as ->; subst t end.
    1: match goal with [ |- sss_output _ _ _ (_, ?st) ] => evar (Vector.t nat (1 + k + n + 3)); enough (st = t) as ->; subst t end.
    1: apply H; try reflexivity. 3: reflexivity.
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

  Fixpoint PREPMORE' (n' : nat) (H : n' <= n) : list (mm_instr (pos (1 + k + n + 3))).
  Proof.
    destruct n'.
    - exact List.nil.
    - refine (List.app (PREPMORE' n' _) _).  1: abstract lia.
      assert (Hn : n' < n) by abstract lia.
      refine (INC (pos_left 3 (pos_right (1 + k) (Fin.of_nat_lt Hn))) :: List.nil).
  Defined. 

  Lemma PREPMORE'_length (n' : nat) (H : n' <= n) : length (PREPMORE' n' H) = n'.
  Proof.
    induction n' in H |- *; cbn.
    - reflexivity.
    - simpl_list. rewrite IHn'. cbn. lia.
  Qed.

  Definition PREPMORE : list (mm_instr (pos (1 + k + n + 3))). refine (@PREPMORE' n _). abstract lia. Defined.

  Lemma PREPMORE'_spec i x (w : Vector.t nat k) n'' n' :
    forall E : n'' + n' = n,
    forall H,
    (i, PREPMORE' n'' H) /MM/ (i, Vector.append (Vector.append (x ## w) (Vector.const 0 n)) (0 ## 0 ## 0 ## vec_nil)) ~~> 
    (i + n'', Vector.append (Vector.append (x ## w) (Vector.cast (Vector.append (Vector.const 1 n'') (Vector.const 0 n')) E)) (0 ## 0 ## 0 ## vec_nil)).
  Proof.
    intros E Hle.
    split. 2:{ cbn. rewrite PREPMORE'_length. lia. }
    revert n' E Hle.
    induction n''; intros n' E Hle.
    - cbn [PREPMORE']. mm sss stop. f_equal.  1: lia.  1: repeat f_equal. cbn. destruct E. now rewrite cast_eq_refl.
    - cbn [PREPMORE'].
      eapply subcode_sss_compute_trans with (P := (i, PREPMORE' n'' (PREPMORE'_subproof n'' Hle))).  1: auto.
      { eapply IHn''. }
      mm sss INC with (pos_left 3 (pos_right (1 + k) (Fin.of_nat_lt (PREPMORE'_subproof0 n'' Hle)))).
      { eexists. eexists. split.  1: reflexivity. now rewrite PREPMORE'_length. }
      mm sss stop. f_equal. 1: lia.
      rewrite <- !vec_app_spec.
      rewrite !vec_pos_app_left.
      rewrite !vec_pos_app_right.
      eapply vec_list_inj. 
      rewrite vec_list_vec_change.
      rewrite !vec_list_vec_app.
      rewrite pos_left_spec.
      rewrite Fin.L_sanity.
      rewrite pos_right_spec.
      rewrite Fin.R_sanity.
      rewrite Fin.to_nat_of_nat. cbn [proj1_sig plus].
      rewrite update_app_left. 2:{ rewrite !app_length, !vec_list_length. lia. }
      f_equal.
      rewrite update_app_right. 2:{ cbn. rewrite !vec_list_length. lia. }
      f_equal. rewrite vec_list_length. replace (S (k + n'') - S k) with n'' by lia.
      rewrite !vec_list_cast.
      rewrite !vec_list_vec_app.
      rewrite update_app_right. 2:{ cbn. rewrite !vec_list_length. lia. }
      rewrite (@vec_list_vec_app nat (S n'') n').
      replace (S n'') with (n'' + 1) by lia.
      rewrite vec_list_length. rewrite Nat.sub_diag. instantiate (2 := 1 + n'). cbn.
      rewrite !vec_list_const. rewrite repeat_app. cbn. rewrite <- !app_assoc.
      f_equal. cbn. f_equal.
      f_equal.
      eapply nth_error_vec_list.
      rewrite vec_list_cast, !vec_list_vec_app; cbn. 
      rewrite nth_error_app2. 2: rewrite vec_list_length; lia.
      now rewrite vec_list_length, Nat.sub_diag.
      Unshelve. lia.
  Qed.

  Lemma PREPMORE_spec i x (w : Vector.t nat k) :
    (i, PREPMORE) /MM/ (i, Vector.append (Vector.append (x ## w) (Vector.const 0 n)) (0 ## 0 ## 0 ## vec_nil)) ~~> 
    (i + n, Vector.append (Vector.append (x ## w) (Vector.const 1 n)) (0 ## 0 ## 0 ## vec_nil)).
  Proof.
    pose proof (PREPMORE'_spec i x w n 0). cbn in H. cbn.
    match goal with [ |- sss_output _ _ _ (_, ?st) ] => evar (Vector.t nat (1 + k + n + 3)); enough (st = t) as ->; subst t end.
    1: eapply H. repeat f_equal.
    eapply vec_list_inj. rewrite vec_list_cast, vec_list_const, <- vec_app_spec, vec_list_vec_app, vec_list_const.
    now simpl_list.
    Unshelve. lia.
  Qed.

  Section POSTP.
  Import ListNotations.

  Definition POSTP (i : nat) : list (mm_instr (pos (1 + k + n + 3))) := 
(*     (*    i *) mm_transfert pos0 (tmp pos2) (tmp pos0) i ++
 *) (*    i *) mm_pop (tmp pos2) (tmp pos0) (tmp pos1) (i) (i+16) (i+16) (i+18) ++
    (* 16+i *)[INC pos0] ++
    (* 17+i *)[DEC (tmp pos0) (i)].
    
  End POSTP.

  Lemma POSTP_length i : length (POSTP i) = 18. Proof. reflexivity. Qed.
  Hint Resolve POSTP_length : core.
  Hint Rewrite POSTP_length : list.

  Lemma POSTP_spec_strong i v out out' :
     v #> pos0 = out' ->
     v #> tmp pos0 = 0 ->
     v #> tmp pos1 = 0 ->
     v #> tmp pos2 = stack_enc (List.repeat true out) ->
     (i, POSTP i) /MM/ (i, v) ~~> (i + 18, v [ (out + out') / Fin.F1 ] [ (stack_enc nil) / tmp pos2] ).
  Proof.
    intros Htgt Htmp0 Htmp1 Htmp2.
    split. 2:{ cbn. lia. }
    induction out in v, Htgt, Htmp0, Htmp1, Htmp2, out', Htgt, Htmp2 |- *.
    - cbn [repeat] in Htmp2. 
      eapply subcode_sss_compute_trans with (P := (i,mm_pop (tmp pos2) (tmp pos0) (tmp pos1) (i) (i+16) (i+16) (i+18))). 1: unfold POSTP; auto.
      { eapply sss_progress_compute. eapply mm_pop_void_progress; eauto. }
      mm sss stop. f_equal. eapply vec_pos_ext. fold plus. intros p.
      eapply (Fin.caseS' p).
      + rewrite vec_change_neq; eauto. rewrite vec_change_eq; eauto.
      + clear p. apply pos_left_right_rect.
        * intros p. rewrite !vec_change_neq; try congruence. intros ? % pos_nxt_inj. fold pos_right in H. eapply pos_right_left. now rewrite H. 
        * intros p. eapply (Fin.caseS' p); clear p.
          -- rewrite !vec_change_neq; try congruence. eapply tmp2_tmp0.
          -- intros p. eapply (Fin.caseS' p); clear p.
             ++ rewrite !vec_change_neq; try congruence. intros H. eapply tmp1_tmp2. cbn. rewrite <- H. reflexivity.
             ++ intros p. eapply (Fin.caseS' p); clear p.
               ** rewrite vec_change_eq. 2: reflexivity. eauto.
               ** eapply Fin.case0.
    - cbn [repeat] in Htmp2. 
      eapply subcode_sss_compute_trans with (P := (i,mm_pop (tmp pos2) (tmp pos0) (tmp pos1) (i) (i+16) (i+16) (i+18))). 1: unfold POSTP; auto.
      { eapply sss_progress_compute. eapply mm_pop_One_progress; eauto. }
      mm sss INC with pos0.  1: unfold POSTP.  1: auto. fold plus in *.
      mm sss DEC zero with (tmp pos0) i.  1: unfold POSTP.  1: auto. 
      {rew vec. rewrite vec_change_neq; eauto. }
      rew vec. specialize IHout with (out' := S out'). 
      replace (out + S out') with (S (out + out')) in IHout by lia.
      match goal with [ |- sss_compute _ _ _ (_, ?st) ] => evar (Vector.t nat (1 + k + n + 3)); enough (st = t) as ->; subst t end.
      1: eapply IHout; rew vec.
      + rewrite vec_change_neq; eauto.
      + rewrite vec_change_neq; eauto.
      + rew vec. symmetry. rewrite vec_change_swap. 2: eauto. rewrite vec_change_idem, vec_change_swap; eauto.
  Qed.

  Lemma POSTP_spec i v out :
     v #> pos0 = 0 ->
     v #> tmp pos0 = 0 ->
     v #> tmp pos1 = 0 ->
     v #> tmp pos2 = stack_enc (List.repeat true out) ->
     (i, POSTP i) /MM/ (i, v) ~~> (i + 18, v [ out / pos0] [ (stack_enc nil) / tmp pos2 ]).
  Proof.
    intros Htgt Htmp0 Htmp1 Htmp2.
    pose proof (POSTP_spec_strong i v out 0 Htgt Htmp0 Htmp1 Htmp2). rewrite Nat.add_0_r in H.
    eapply H.
  Qed.

  Definition PREPALL i := PREP i ++ PREPMORE ++ INC pos0 :: List.nil.

  Lemma PREPALL_length i : length (PREPALL i) = k * 14 + n + 1.
  Proof. unfold PREPALL, PREPMORE; rewrite !app_length, PREP_length, PREPMORE'_length; cbn; lia. Qed.

  Lemma PREPALL_spec i v : 
    (i, PREPALL i) /MM/ (i, Vector.append (Vector.append (0 ## v) (Vector.const 0 n)) (0 ## 0 ## 0 ## vec_nil)) ~~>
          (i + k * 14 + n + 1, Vector.append (Vector.append (stack_enc nil ## Vector.map (fun n => stack_enc (List.repeat true n)) v) (Vector.const (stack_enc nil) n)) (0 ## 0 ## 0 ## vec_nil)).
  Proof.
    split. 2: cbn; rewrite PREPALL_length; lia.
    eapply subcode_sss_compute_trans. 2: eapply PREP_spec. 1: unfold PREPALL; auto.
    eapply subcode_sss_compute_trans. 2: eapply PREPMORE_spec. 1: unfold PREPALL; auto.
    mm sss INC with pos0.
    { unfold PREPALL. eexists. eexists nil. cbn. split.  1: now rewrite app_assoc.
      rewrite app_length, PREP_length; unfold PREPMORE; rewrite PREPMORE'_length. lia. }
    fold plus. mm sss stop.
    f_equal. lia.
  Qed.

End preprocess.

Lemma cast_cast {n m} {E : n = m} {X} (v : Vector.t X n) (E2 : m = n) :
  cast (cast v E) E2 = v.
Proof.
  destruct E. now rewrite !cast_eq_refl.
Qed.

Definition cases {k i} : (forall p : pos (1 + k + i + 3),
{p = pos_right (1 + k + i) pos0} + {p = pos_right (1 + k + i) pos1} + {p = pos_right (1 + k + i) pos2} +
{q : pos (1 + k + i) | p = pos_left 3 q}).
Proof.
  apply pos_left_right_rect; [ eauto | ].
  intros p. eapply (Fin.caseS' p); [ eauto | ].
  intros p'. eapply (Fin.caseS' p'); [ eauto | ].
  intros p''. eapply (Fin.caseS' p''); [ eauto | ].
  eapply Fin.case0.
Defined.

Lemma vec_pos_const {k} {X x} (p : pos k) : @const X x k #> p = x.
Proof.
  induction p; cbn; eauto.
Qed.

Lemma BSM_computable_to_MM_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  BSM_computable R -> MM_computable R.
Proof.
  intros (i & n & P & HP1 & HP2) % BSM_computable_iff. eapply MM_computable_iff.
  unshelve (epose proof (@bsm_mm_compiler_strong (1 + k + i) n P (pos_right _ Fin.F1) (pos_right _ (Fin.FS Fin.F1)) (pos_right _ (pos2)) (pos_left _) (1 + length (PREPALL k i 1)) _ _ _ _ ) as HQ0; edestruct HQ0 as [Q HQ]).
  - eapply tmp0_tmp1.
  - intros p. intros H. eapply  pos_right_left. now rewrite H.
  - intros.  intros H. eapply  pos_right_left. now rewrite H.
  - now intros ? ? ? % pos_left_inj.
  - exact cases.
  - intros ? % pos_right_inj; congruence.
  - intros ? % pos_right_inj % pos_nxt_inj. congruence.
  - intros p. intros H. eapply  pos_right_left. now rewrite H.
  - exists (i + 3).   assert (E : 1 + k + i + 3 = (1 + k) + (i + 3)) by lia.
    pose (q' := PREPALL k i 1 ++ Q ++ mm_transfert pos0 (pos_right (1 + k + i) pos2) (pos_right (1 + k + i) pos0) (1 + length (PREPALL k i 1) + length Q) ++ POSTP k i (4 + length (PREPALL k i 1) + length Q)).
    assert (Eq1 : forall v, cast (append (append (0 ## v) (const 0 i)) (const 0 3)) E = append (0 ## v) (const 0 (i + 3))).
      { intros v. clear. cbn.
        f_equal. match goal with [ |- context [@f_equal ?A ?B ?f ?x ?y ?e]] => generalize (@f_equal A B f x y e) end. clear.
        induction v; cbn; intros E.
        - induction i in E |- *; cbn.
          + reflexivity.
          + now rewrite IHi.
        - f_equal. now rewrite IHv.
      }
    exists (MM_cast q' E). fold plus. split.
    + intros v m. intros ? % HP1.
      setoid_rewrite eval_iff.
      destruct H as (c & v' & H % BSM_sss.eval_iff). fold plus in *.
      eapply HQ in H. 
      eexists. eexists ?[v']. rewrite <- Eq1.
      unshelve eassert (Eq2 : forall v' : Vector.t nat (k + (i + 3)), m ## v' = cast (m ## _) E).
      { fold plus. refine (Vector.cast v' _). abstract lia. }
      { clear. intros v. cbn. f_equal.
        match goal with [ |- context [@f_equal ?A ?B ?f ?x ?y ?e]] => generalize (@f_equal A B f x y e) end. fold plus.
        intros E2. generalize (BSM_computable_to_MM_computable_subproof k i E).
        clear. intros E1. cbn in *. revert v E1 E2. generalize (k + i + 2).  generalize (k + (i + 2)). clear. intros.
        destruct E1. now rewrite !cast_eq_refl.
      }
      rewrite Eq2.
      instantiate (v' := (cast _ _)).
      rewrite <- @MM_cast_spec. subst q'.
      split. 
      1: { eapply subcode_sss_compute_trans. 2: eapply PREPALL_spec. 1: auto.
      match goal with [H : sss_output _  _ ?st1 _ |- sss_compute _ _ ?st2 _ ] => enough (st1 = st2) end.
      1: rewrite H0 in H.
      1: eapply subcode_sss_compute_trans. 2: eapply H.  1: auto.
      2:{ f_equal.  1: rewrite PREPALL_length.  1: lia. clear.
          eapply vec_pos_ext. intros p.
          unfold vec_enc. rewrite vec_pos_set. destruct (cases p) as [ [[-> | ->] | ->] | [q ->]].
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - rewrite <- !vec_app_spec. rewrite vec_pos_app_left.
            revert q. eapply pos_left_right_rect.
            + intros p. rewrite !vec_pos_app_left.
              rewrite <- !vec_map_spec. eapply (Fin.caseS' p).
              * cbn. reflexivity.
              * cbn. intros. rewrite !vec_pos_map. reflexivity.
            + intros p. rewrite !vec_pos_app_right.
              now rewrite !vec_pos_const.
      }
      eapply subcode_sss_compute_trans with (P := (1 + length (PREPALL k i 1) + length Q, mm_transfert pos0 (pos_right (1 + k + i) pos2) (pos_right (1 + k + i) pos0) (1 + length (PREPALL k i 1) + length Q))).
      { eexists (PREPALL k i 1 ++ Q). eexists (POSTP _ _ _). split. 1:  now rewrite <- app_assoc. rewrite !app_length, PREPALL_length. lia. }
      1: eapply sss_progress_compute.  1: eapply mm_transfert_progress.
      1-5: clear.
      { cbn. congruence. }
      { cbn. congruence. } 
      { cbn. intros ? % pos_nxt_inj % pos_right_inj. congruence. }
      { unfold vec_enc. rewrite vec_pos_set.
        destruct cases as [ [ [| ] | ] | [q Hq]]; rew vec.
        exfalso. eapply pos_right_left. now rewrite Hq. }
      { unfold vec_enc. rewrite vec_pos_set. 
        destruct cases as [ [ [| ] | ] | [q Hq]]; rew vec.
        exfalso. eapply pos_right_left. now rewrite Hq. }
      { reflexivity. }
      eapply subcode_sss_compute_trans with (P := (4 + length (PREPALL k i 1) + length Q, POSTP k i (4 + length (PREPALL k i 1) + length Q))).
      { eexists _. eexists List.nil. split.  1: rewrite app_nil_r.  1: now rewrite !app_assoc. rewrite !app_length, PREPALL_length. cbn. lia. }
      1: eapply POSTP_spec.
      { unfold vec_enc. rewrite vec_pos_set. destruct cases as [ [ | ] | [q Hq]]; rew vec. }
      { unfold vec_enc. rewrite !vec_pos_set.
        destruct cases as [ [ [| ] | ] | [q Hq]]; rew vec.
        all: try now (cbn in e; congruence).
        revert Hq. eapply (Fin.caseS' q).
        all: try now (cbn; congruence).
        intros _. rewrite vec_change_neq. 2: intros ? % pos_right_inj; congruence.
        rewrite vec_change_neq. 2: cbn; congruence.
        rewrite vec_pos_set.
        destruct cases as [ [ [| ] | ] | [q' Hq']]; rew vec.
        exfalso. eapply pos_right_left. now rewrite Hq'. }
      {  unfold vec_enc. rewrite !vec_pos_set.
         destruct cases as [ [ [| ] | ] | [q Hq]]; rew vec.
         { rewrite vec_pos_set. destruct cases as [ [ [| ] | ] | [q' Hq']]; rew vec.
         exfalso. eapply pos_right_left. now rewrite Hq'. }
         { rewrite vec_pos_set. destruct cases as [ [ [| ] | ] | [q' Hq']]; rew vec.
         exfalso. eapply pos_right_left. now rewrite Hq'. }
         { rewrite vec_change_neq. 2: intros ? % pos_right_inj % pos_nxt_inj; congruence.
           rewrite vec_change_neq. 2: cbn; congruence.
           rewrite vec_pos_set.
           destruct cases as [ [ [| ] | ] | [q' Hq']]; rew vec.
           exfalso. eapply pos_right_left. now rewrite Hq'. }
      }
      2:{  fold plus.
      mm sss stop. cbn. f_equal.
      rewrite cast_cast.
      reflexivity.
      }
      {  unfold vec_enc. rewrite !vec_pos_set. destruct cases as [ [ [| ] | ] | [q' Hq']]; rew vec.
         all: try now (cbn in e; congruence).
         revert Hq'. eapply (Fin.caseS' q').
         all: try now (cbn; congruence). }
      Unshelve. lia.
      }
      cbn. autorewrite with list. cbn. setoid_rewrite PREPALL_length. right. lia.
    + intros v H2.
      eapply HP2. eapply HQ. eapply MM_cast_terminates with (E := E).
      eapply subcode_sss_terminates.
      2:{ eapply subcode_sss_terminates_inv.  1: eapply mm_sss_fun.
      1: eapply H2. 
          2:{rewrite <- Eq1. rewrite <- MM_cast_spec.
             rewrite PREPALL_length. cbn [plus].
             match goal with [ |- sss_output _ _ _ (_, ?st) ] => evar (t : Vector.t nat (1 + k + i + 3)); enough (Eq : st = t) end; subst t.
             1: rewrite Eq.  1: eapply PREPALL_spec. 

             clear.
          eapply vec_pos_ext. intros p.
          unfold vec_enc. rewrite vec_pos_set. destruct (cases p) as [ [[-> | ->] | ->] | [q ->]].
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - cbn. rewrite <- !vec_app_spec. now rewrite vec_pos_app_right.
          - rewrite <- !vec_app_spec. rewrite vec_pos_app_left.
            revert q. eapply pos_left_right_rect.
            + intros p. repeat setoid_rewrite vec_pos_app_left.
              repeat setoid_rewrite <- vec_map_spec. eapply (Fin.caseS' p).
              * cbn. reflexivity.
              * intros. repeat setoid_rewrite vec_pos_map.
                f_equal. rewrite (@vec_pos_app_left (list bool) (1 + k) i).
                cbn. rewrite vec_pos_map. reflexivity.
            + intros p. rewrite !vec_pos_app_right.
              rewrite (@vec_pos_app_right (list bool) (S k) i).
              now rewrite !vec_pos_const.
          }
 
      clear. subst q'. generalize (PREPALL k i 1).
      intros l.
      generalize (mm_transfert pos0 (pos_right (1 + k + i) pos2) (pos_right (1 + k + i) pos0) (1 + length l + length Q) ++ POSTP k i (4 + length l + length Q)).
      fold plus. revert l. destruct E. cbn. intros. exists nil. cbn. eauto.
      }

      clear. subst q'.
      generalize (PREPALL k i 1).
      intros l.
      generalize (mm_transfert pos0 (pos_right (1 + k + i) pos2) (pos_right (1 + k + i) pos0) (1 + length l + length Q) ++ POSTP k i (4 + length l + length Q)).
      fold plus. revert l. destruct E. cbn. intros. exists l. cbn. eauto.
Qed.
