From Undecidability.H10 Require Import H10 dio_single dio_logic.
From Undecidability.L.Datatypes Require Import LNat LOptions LSum.
From Undecidability.L.Datatypes.List Require Import List_basics List_eqb List_fold List_enc.

From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared Require Import DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import recalg ra_bs ra_sem_eq.

Reserved Notation "  '[' f ';' v ';' min ';' c ']' '~~>' x " (at level 70).

(* Bigstep semantics for recursive algorithms *)
   
Inductive ra_bs_c : nat -> nat -> forall k, recalg k -> vec nat k -> nat -> Prop := 
    | in_ra_bs_c_cst  : forall min c n v,             [ra_cst n;        v; min; S c] ~~> n
    | in_ra_bs_c_zero : forall min c v,               [ra_zero;         v; min; S c] ~~> 0
    | in_ra_bs_c_succ : forall min c v,               [ra_succ;         v; min; S c] ~~> S (vec_head v)
    | in_ra_bs_c_proj : forall min c k v j,           [@ra_proj k j;    v; min; S c] ~~> vec_pos v j 
    
    | in_ra_bs_c_comp : forall min c k i f (gj : vec (recalg i) k) v w x,
                                         (forall j, [vec_pos gj j;    v; min; c - pos2nat j] ~~> vec_pos w j)
                                 ->             [f;               w; min; S c] ~~> x
                                 ->             [ra_comp f gj;    v; min; S (S c)] ~~> x

    | in_ra_bs_c_rec_0 : forall min c k f (g : recalg (S (S k))) v x,    
                                               [f;               v; min; c] ~~> x 
                                 ->             [ra_rec f g;   0##v; min; S c] ~~> x

    | in_ra_bs_c_rec_S : forall min c k f (g : recalg (S (S k))) v n x y,          
                                             [ra_rec f g;   n##v; min; c] ~~> x
                               ->             [g;         n##x##v; min; c] ~~> y
                               ->             [ra_rec f g; S n##v; min; S c] ~~> y
                               
    | in_ra_bs_c_min : forall min c k (f : recalg (S k)) v x w , x >= min ->
                           (forall j : pos x, pos2nat j >= min -> [f;    pos2nat j##v; 0; c - (pos2nat j - min)] ~~> S (vec_pos w j)) 
                                             ->             [f;            x##v; 0; c - (x - min)] ~~> 0
                                             ->             [ra_min f;        v; min; S c] ~~> x
where " [ f ; v ; min ; c ] ~~> x " := (@ra_bs_c min c _ f v x).

Lemma ra_bs_mono min k (f : recalg k) v c1 x :
  [f ; v ; min ; c1 ] ~~> x -> forall c2, c1 <= c2 -> [f ; v ; min; c2] ~~> x. 
Proof.
  induction 1; intros; try (destruct c2;[ lia | ]).
  - econstructor.
  - econstructor.
  - econstructor.
  - econstructor.
  - destruct c2; try lia. econstructor.
    + intros. eapply H0. lia.
    + eapply IHra_bs_c. lia.
  - econstructor. eapply IHra_bs_c. lia.
  - econstructor.
    + eapply IHra_bs_c1. lia.
    + eapply IHra_bs_c2. lia.
  - econstructor.
    + lia.
    + intros. eapply H1. lia. lia.
    + eapply IHra_bs_c. lia.
Qed.

Lemma vec_sum_le:
  forall (k : nat) (cst : vec nat k) (j : pos k), vec_pos cst j <= vec_sum cst.
Proof.
  intros k cst j.
  induction cst; cbn.
  - invert pos j.
  - invert pos j.
    + lia. 
    + specialize (IHcst j); lia.
Qed.

Lemma ra_bs_from_c k (f : recalg k) c v x :
 [f ; v ; 0 ; c] ~~> x -> [ f; v ] ~~> x.
Proof.
  remember 0 as min.
  induction 1; subst; eauto using ra_bs.
  econstructor.
  + intros; eapply H1; lia.
  + auto.
Qed.

Lemma ra_bs_to_c k (f : recalg k) v x :
  [ f; v ] ~~> x -> exists c, [f ; v ; 0 ; c] ~~> x.
Proof.
  induction 1.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - destruct IHra_bs as [c].
    eapply vec_reif in H0 as [cst].
    exists (2 + c + vec_sum cst + k). cbn.
    econstructor.
    + intros. eapply ra_bs_mono. eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); lia.
      enough (vec_pos cst j <= vec_sum cst).
      lia. eapply vec_sum_le.
    + eapply ra_bs_mono. eauto. lia.
  - destruct IHra_bs as [c]. exists (S c). now econstructor.
  - destruct IHra_bs1 as [c1].
    destruct IHra_bs2 as [c2].
    exists (1 + c1 + c2).
    cbn. econstructor.
    + eapply ra_bs_mono. eauto. lia.
    + eapply ra_bs_mono. eauto. lia.
  - destruct IHra_bs as [c].
    eapply vec_reif in H0 as [cst].
    exists (1 + c + vec_sum cst + x). cbn.
    econstructor. lia. 
    + intros. eapply ra_bs_mono. eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); lia.
      enough (vec_pos cst j <= vec_sum cst) by lia.
      eapply vec_sum_le.
    + eapply ra_bs_mono. eauto. lia.
Qed.

Local Hint Resolve ra_bs_from_c ra_bs_to_c : core.

Fact ra_bs_c_correct k (f : recalg k) v x :
  [|f|] v x <-> exists c, [f ; v ; 0 ; c] ~~> x.
Proof.
  rewrite ra_bs_correct; split; auto.
  intros (c & H); revert H; apply ra_bs_from_c.
Qed.

(*
Inductive reccode :=
| rc_cst (n : nat)
| rc_zero
| rc_succ
| rc_proj (n : nat)
| rc_comp (f : reccode) (g : reccode)
| rc_cons (f : reccode) (g : reccode)
| rc_nil
| rc_rec (f : reccode) (g : reccode)
| rc_min (f : reccode).

Fixpoint eval (fuel : nat) (min : nat) (c : reccode) (v : list nat) : option (nat + list nat) :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | rc_cst n => Some (inl n)
    | rc_zero => Some (inl 0)
    | rc_succ => match v with
                | x :: _ => Some (inl (S x))
                | _ => None
                end
    | rc_proj n => match nth_error v n with Some r => Some (inl r) | None => None end
    | rc_comp f g => match eval fuel min g v
                    with
                    | Some (inr g) => match eval fuel min f g with Some (inl f) => Some (inl f) | _ => None end
                    | _ => None
                    end
    | rc_cons f g => match eval fuel min f v, eval fuel min g v with
                    | Some (inl f), Some (inr g) => Some (inr (f :: g))
                    | _, _ => None
                    end
    | rc_nil => Some (inr nil)
    | rc_rec f g => match v with
                   | 0 :: v => match eval fuel min f v with Some (inl r) => Some (inl r) | _ => None end
                   | S n :: v => match eval fuel min (rc_rec f g) (n :: v) with
                               | Some (inl y) => match eval fuel min g (n :: y :: v) with Some (inl r) => Some (inl r) | _ => None end
                               | _ => None
                               end
                   | _ => None
                   end
    | rc_min f => match eval fuel 0 f (min :: v) with
                 | Some (inl 0) => Some (inl min)
                 | Some (inl _) => match eval fuel (S min) (rc_min f) v with Some (inl r) => Some (inl r) | _ => None end
                 | _ => None
                 end
    end
  end.
*)

Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.

Definition rec_erase i (erase : forall i, recalg i -> reccode) := (fix rec k (v : vec (recalg i) k) := match v with vec_nil => rc_nil | x ## v => rc_cons (erase _ x) (rec _ v) end).

Fixpoint erase k (f : recalg k) : reccode :=
  match f with
  | ra_cst n => rc_cst n
  | ra_zero => rc_zero
  | ra_succ => rc_succ
  | ra_proj _ p => rc_proj (pos2nat p)
  | ra_comp _ _ f g => rc_comp (erase f) (rec_erase erase g)
  | ra_rec _ f g => rc_rec (erase f) (erase g)
  | ra_min _ f => rc_min (erase f)
  end.

Lemma vec_list_nth:
  forall (k : nat) (p : pos k) (v : vec nat k), nth_error (vec_list v) (pos2nat p) = Some (vec_pos v p).
Proof.
  intros k p v.
  induction v.
  - invert pos p.
  - cbn; invert pos p.
    + reflexivity.
    + eapply IHv.
Qed.

Lemma eval_inv n min i k (v : vec (recalg i) k) a l :
  eval n min (rec_erase erase v) a = Some (inr l) ->
  exists x, vec_list x = l /\
  (forall j : pos k, eval (n -S (pos2nat j)) min (erase (vec_pos v j)) a = Some (inl (vec_pos x j))).
Proof.
  induction v in n,l |- *.
  - destruct n; cbn. 
    firstorder congruence.
    exact vec_nil. 
    intros [=]; subst.
    exists vec_nil. 
    split; auto.
    intro j; invert pos j.
  - destruct n. inversion 1.
    intros ?. cbn in H.
    destruct (eval n) eqn:E1; try congruence.
    destruct s; try congruence.
    destruct (eval n min (rec_erase erase v) a) eqn:E2; try congruence.
    destruct s; try congruence. inv H. 
    edestruct IHv as (? & ? & ?). eauto.
    exists (n1 ## x). split. cbn. firstorder congruence.
    intros j; pos_inv j.
    + rewrite pos2nat_fst in *. assert (S n - 1 = n) by lia. rewrite H1 in *.
      cbn -[eval].  eassumption.
    + rewrite pos2nat_nxt.
      specialize (H0 j). 
      assert (S n - S (S (pos2nat j)) = n - S (pos2nat j)) by lia. rewrite H1 in *.
      cbn. rewrite H0. reflexivity.
Qed.

Lemma le_ind2 m (P : nat -> Prop) :
  P m -> (forall n, P (S n) -> S n <= m -> P n) -> forall n, n <= m -> P n.
Proof.
  intros. induction H1.
  - eauto.
  - eauto.
Qed. 

Lemma vec_pos_gt n X (w : vec X n) j k n1:
  pos2nat k < pos2nat j ->
  vec_pos w j = vec_pos (vec_change w k n1) j.
Proof.
  intros.
  induction w.
  - invert pos j.
  - invert pos j; cbn.
    + invert pos k; cbn; auto; lia.
    + invert pos k; cbn; auto.
      apply IHw. 
      rewrite !pos2nat_nxt in H; lia.
Qed.

Lemma erase_correct k min (f : recalg k) v n c  :
  (ra_bs_c min c f v n <-> eval c min (erase f) (vec_list v) = Some (inl n)).
Proof.
  revert all except c.
  pattern c. eapply lt_wf_ind. intros.
  destruct f; cbn. 
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H4. subst.
      reflexivity. 
    + destruct n; inversion 1. subst. econstructor.
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H3. subst.
      reflexivity.
    + destruct n; inversion 1. subst. econstructor.
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H3. subst.
      cbn; revert H0; vec split v with x; auto. 
    + destruct n; inversion 1. 
      revert H0 H2; vec split v with x; cbn.
      intros [=] _; subst; constructor.
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H5. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H6. subst.
      cbn. rewrite vec_list_nth. reflexivity.
    + destruct n; inversion 1. rewrite vec_list_nth in H2. inv H2. econstructor.
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H2. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H7. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H7. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H8. subst.
      assert (forall j : pos k, eval (c0 - pos2nat j) min (erase (vec_pos t j)) (vec_list v) = Some (inl (vec_pos w j))).
      intros. eapply H. lia.
                                      
      cbn. eapply H. lia. eapply H. lia. specialize (H9 j).
      eapply H in H9. 2:lia. eapply H. lia. eauto.
      remember (S c0) as c'. cbn.

      assert (eval c' min (rec_erase erase t) (vec_list v) = Some (inr (vec_list w))).
      { subst. clear - H1. revert c0 H1. induction t; intros.
        - cbn; vec nil w; reflexivity.
        - cbn. pose proof (H1 pos_fst). cbn in H. rewrite pos2nat_fst in H.
          replace (c0 - 0) with c0 in H by lia. rewrite H.
          revert H1 H; vec split w with y; intros H1 H.
          destruct c0. cbn in H. inv H. erewrite IHt.
          reflexivity.
          intros. specialize (H1 (pos_nxt j)). rewrite pos2nat_nxt in H1.
          eassumption.
      }
      rewrite H2. subst. eapply H in H10. rewrite H10. reflexivity. lia.
    + destruct n; inversion 1.
      destruct (eval n min (rec_erase erase t) (vec_list v)) eqn:E; try congruence.
      destruct s; try congruence.
      destruct (eval n min (erase f) l) eqn:E2; try congruence.
      destruct s; try congruence. inv H2.
      destruct n; try now inv E2.

      destruct (list_vec_full l). 
      destruct (eval_inv E) as (w & ? & ?). subst.

      eapply in_ra_bs_c_comp with (w := w).
      * intros. eapply H. lia. specialize (H2 j). assert (S n - S (pos2nat j) = n - pos2nat j) by lia. rewrite H1 in *.
        eauto.
      * eapply H. lia. eassumption.
  - split. inversion 1.
    + eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H4. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H6. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H7. subst.
      cbn.
      eapply H in H8. 2:lia. rewrite H8. reflexivity.
    + eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H2. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H5. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H6. subst.
      eapply H in H7.
      cbn. 2:lia. cbn in H7. rewrite H7.
      eapply H in H9. 2:lia. cbn in H9. rewrite H9. reflexivity.
    + intros. destruct n; inv H0.
      revert H2; vec split v with n1; cbn; intros H2.
      destruct n1.
      * destruct (eval n min (erase f1) (vec_list v)) eqn:E.
        destruct s; inv H2.
        -- econstructor. eapply H. lia. eauto.
        -- econstructor. congruence.
      * destruct eval eqn:E2; try congruence.
        destruct s; try congruence.
        destruct (eval n min (erase f2)) eqn:E3.
        destruct s; inv H2.
        -- econstructor. eapply H. lia. eauto. eapply H. lia. eauto.
        -- congruence.
  - split.
    + inversion 1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H1. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H2. subst.
      clear H0. unfold ge in *.
      revert c0 H w H7 H8. pattern n0. revert min H3.
      eapply le_ind2; intros.
      * cbn in *. eapply H in H8. 2:lia.
        assert (c0 - (n0 - n0) = c0) by lia. rewrite H0 in *.
        cbn in H8. rewrite H8. reflexivity.
      * destruct n0; try lia.
        assert (n < S n0) by lia.
        assert (H10 := H7).
        specialize (H7 (nat2pos H2)). rewrite pos2nat_nat2pos in H7.
        assert (n <= n) by lia. eapply H7 in H3.
        eapply H1 in H3. 2: lia. cbn.
        assert (c0 - (n - n) = c0) by lia. rewrite H4 in *. cbn in H3. rewrite H3.

        assert (eval c0 (S n) (rc_min (erase f)) (vec_list v) = Some (inl (S n0))).
        eapply H1 with (f := ra_min f). lia.

        destruct c0. inv H3.
        econstructor. lia.
           
        intros ? ?. specialize (H10 j).
        assert (S c0 - (pos2nat j - n) = c0 - (pos2nat j - S n)) by lia.
        rewrite H6 in *.  eapply H10. lia.
        assert (S c0 - (S n0 - n) = c0 - (S n0 - S n)) by lia. rewrite H5 in *.
        eassumption.
        now rewrite H5.
    + intros.
      destruct n; try now inv H0. cbn in H0.
      destruct (eval n) eqn:E1; try now inv H0.
      destruct s; try congruence.
      destruct n1; inv H0.
      * econstructor. lia. intros. pose proof (pos2nat_prop j). lia.
        eapply H. lia. assert (n - (n0 - n0) = n) as -> by lia. eassumption.
      * destruct (eval n (S min)) eqn:E2; try now inv H2.
        destruct s; inv H2.
        eapply H with (f := ra_min f) in E2. 2:lia.
        eapply H with (v := vec_cons min v) in E1. 2:lia.
        inversion E2; subst.
        eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H0. subst.
        eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H1. subst.
        assert (min < n0) by lia.
        eapply in_ra_bs_c_min with (w := vec_change w (nat2pos H0) n1).
        -- lia.
        -- intros. inversion H1.
           ++ subst.
              rewrite nat2pos_pos2nat.
              rewrite vec_change_eq. 2:reflexivity.
              assert (S c0 - (pos2nat j - pos2nat j) = S c0) as -> by lia.
              eassumption.
           ++ specialize (H6 j).
              assert (S c0 - (S m - min) = c0 - (pos2nat j - S min)) by lia. rewrite H5 in *.
              enough (vec_pos w j = vec_pos (vec_change w (nat2pos H0) n1) j).
              rewrite H8 in H6. rewrite H3. eapply H6. lia.
              assert (pos2nat j > min) by lia.
              eapply vec_pos_gt.
              rewrite pos2nat_nat2pos. lia.
        -- assert (S c0 - (n0 - min) = c0 - (n0 - S min)) by lia. rewrite H1. eassumption.
           Unshelve. exact vec_zero.
Qed.

Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.

Definition evalfun fuel c v := match eval fuel 0 c v with Some (inl x) => Some x | _ => None end.

Definition UMUREC_HALTING c := exists fuel, evalfun fuel c nil <> None.

Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Lemma MUREC_red : MUREC_HALTING ⪯ UMUREC_HALTING.
Proof.
  unshelve eexists.
  - intros f. exact (erase f).
  - unfold UMUREC_HALTING, MUREC_HALTING. 
    intros f.
    split; intros [].
    + rewrite ra_bs_correct in H. eapply ra_bs_to_c in H as [].
      exists x0. eapply erase_correct in H. unfold evalfun. cbn in H. rewrite H. congruence.
    + unfold evalfun in H. destruct eval eqn:E; try congruence.
      destruct s; try congruence.
      eapply erase_correct with (v := vec_nil) in E.
      exists n. eapply ra_bs_correct. now eapply ra_bs_from_c.
Qed.

Local Definition r := (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).

Lemma MUREC_WCBV : MUREC_HALTING ⪯ converges.
Proof.
  eapply reduces_transitive. eapply MUREC_red.
  eapply L_recognisable_halt.
  exists (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).
  split.
  - econstructor. extract.
  - firstorder.
    + unfold evalfun in *. exists x0. destruct eval; try destruct s; try congruence.
    + exists x0. unfold evalfun in *. destruct eval; try destruct s; try congruence.
Qed.

(* Print Assumptions MUREC_WCBV. *)
