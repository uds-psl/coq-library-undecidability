Set Default Goal Selector "!".

From Undecidability.H10 Require Import H10 dio_single dio_logic.
From Undecidability.L.Datatypes Require Import LNat LOptions LSum.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared Require Import DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import MuRec recalg ra_sem_eq.

Reserved Notation "  '[' f ';' v ';' min ';' c ']' '▹' x " (at level 70).

(* Bigstep semantics for recursive algorithms *)
   
Inductive ra_bs_c : nat -> nat -> forall k, recalg k -> vec nat k -> nat -> Prop := 
    | in_ra_bs_c_cst  : forall min c n v,             [ra_cst n;        v; min; S c] ▹ n
    | in_ra_bs_c_zero : forall min c v,               [ra_zero;         v; min; S c] ▹ 0
    | in_ra_bs_c_succ : forall min c v,               [ra_succ;         v; min; S c] ▹ S (vec_head v)
    | in_ra_bs_c_proj : forall min c k v j,           [@ra_proj k j;    v; min; S c] ▹ vec_pos v j 
    
    | in_ra_bs_c_comp : forall min c k i f (gj : vec (recalg i) k) v w x,
                                         (forall j, [vec_pos gj j;    v; min; c - pos2nat j] ▹ vec_pos w j)
                                 ->             [f;               w; min; S c] ▹ x
                                 ->             [ra_comp f gj;    v; min; S (S c)] ▹ x

    | in_ra_bs_c_rec_0 : forall min c k f (g : recalg (S (S k))) v x,    
                                               [f;               v; min; c] ▹ x 
                                 ->             [ra_rec f g;   0##v; min; S c] ▹ x

    | in_ra_bs_c_rec_S : forall min c k f (g : recalg (S (S k))) v n x y,          
                                             [ra_rec f g;   n##v; min; c] ▹ x
                               ->             [g;         n##x##v; min; c] ▹ y
                               ->             [ra_rec f g; S n##v; min; S c] ▹ y
                               
    | in_ra_bs_c_min : forall min c k (f : recalg (S k)) v x w , x >= min ->
                           (forall j : pos x, pos2nat j >= min -> [f;    pos2nat j##v; 0; c - (pos2nat j - min)] ▹ S (vec_pos w j)) 
                                             ->             [f;            x##v; 0; c - (x - min)] ▹ 0
                                             ->             [ra_min f;        v; min; S c] ▹ x
where " [ f ; v ; min ; c ] ▹ x " := (@ra_bs_c min c _ f v x).

Lemma ra_bs_mono min k (f : recalg k) v c1 x :
  [f ; v ; min ; c1 ] ▹ x -> forall c2, c1 <= c2 -> [f ; v ; min; c2] ▹ x. 
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
    + intros. eapply H1; lia.
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
 [f ; v ; 0 ; c] ▹ x -> [ f; v ] ▹ x.
Proof.
  remember 0 as min.
  induction 1; subst; eauto using ra_bs.
  econstructor.
  + intros; eapply H1; lia.
  + auto.
Qed.

Lemma ra_bs_to_c k (f : recalg k) v x :
  [ f; v ] ▹ x -> exists c, [f ; v ; 0 ; c] ▹ x.
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
    + intros. eapply ra_bs_mono. 1:eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); lia.
      enough (vec_pos cst j <= vec_sum cst).
      1: lia. eapply vec_sum_le.
    + eapply ra_bs_mono. 1: eauto. lia.
  - destruct IHra_bs as [c]. exists (S c). now econstructor.
  - destruct IHra_bs1 as [c1].
    destruct IHra_bs2 as [c2].
    exists (1 + c1 + c2).
    cbn. econstructor.
    + eapply ra_bs_mono. 1: eauto. lia.
    + eapply ra_bs_mono. 1: eauto. lia.
  - destruct IHra_bs as [c].
    eapply vec_reif in H0 as [cst].
    exists (1 + c + vec_sum cst + x). cbn.
    econstructor. 1: lia. 
    + intros. eapply ra_bs_mono. 1: eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); lia.
      enough (vec_pos cst j <= vec_sum cst) by lia.
      eapply vec_sum_le.
    + eapply ra_bs_mono. 1: eauto. lia.
Qed.

Local Hint Resolve ra_bs_from_c ra_bs_to_c : core.

Fact ra_bs_c_correct k (f : recalg k) v x :
  [|f|] v x <-> exists c, [f ; v ; 0 ; c] ▹ x.
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
    + firstorder congruence.
      exact vec_nil. 
    + intros [=]; subst.
      exists vec_nil. 
      split; auto.
      intro j; invert pos j.
  - destruct n. 1: inversion 1.
    intros ?. cbn in H.
    destruct (eval n) eqn:E1; try congruence.
    destruct s; try congruence.
    destruct (eval n min (rec_erase erase v) a) eqn:E2; try congruence.
    destruct s; try congruence. inv H. 
    edestruct IHv as (? & ? & ?). 1: eauto.
    exists (n1 ## x). split. 1: cbn; firstorder congruence.
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
  revert k min f v n.
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
      { intros. eapply H. 1: lia. 
                                      
      cbn. eapply H. 1: lia. eapply H. 1: lia. specialize (H9 j).
      eapply H in H9. 2:lia. eapply H. 1: lia. eauto. }
      
      remember (S c0) as c'. cbn.

      assert (eval c' min (rec_erase erase t) (vec_list v) = Some (inr (vec_list w))).
      { subst. clear - H1. revert c0 H1. induction t; intros.
        - cbn; vec nil w; reflexivity.
        - cbn. pose proof (H1 pos_fst). cbn in H. rewrite pos2nat_fst in H.
          replace (c0 - 0) with c0 in H by lia. rewrite H.
          revert H1 H; vec split w with y; intros H1 H.
          destruct c0. 1: cbn in H. 1: inv H. erewrite IHt.
          1: reflexivity.
          intros. specialize (H1 (pos_nxt j)). rewrite pos2nat_nxt in H1.
          eassumption.
      }
      rewrite H2. subst. eapply H in H10. 1: rewrite H10. 1: reflexivity. lia.
    + destruct n; inversion 1.
      destruct (eval n min (rec_erase erase t) (vec_list v)) eqn:E; try congruence.
      destruct s; try congruence.
      destruct (eval n min (erase f) l) eqn:E2; try congruence.
      destruct s; try congruence. inv H2.
      destruct n; try now inv E2.

      destruct (list_vec_full l). 
      destruct (eval_inv E) as (w & ? & ?). subst.

      eapply in_ra_bs_c_comp with (w := w).
      * intros. eapply H. 1: lia. specialize (H2 j). assert (S n - S (pos2nat j) = n - pos2nat j) by lia. rewrite H1 in *.
        eauto.
      * eapply H. 1: lia. eassumption.
  - split. 1: inversion 1.
    + eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H4. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H6. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H7. subst.
      cbn.
      eapply H in H8. 2:lia. rewrite H8. reflexivity.
    + eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H2. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H5. subst.
      eapply (Eqdep_dec.inj_pair2_eq_dec _ nat_eq_dec) in H6. subst.
      eapply H in H7.
      1: cbn. 2:lia. cbn in H7. rewrite H7.
      eapply H in H9. 2:lia. cbn in H9. rewrite H9. reflexivity.
    + intros. destruct n; inv H0.
      revert H2; vec split v with n1; cbn; intros H2.
      destruct n1.
      * destruct (eval n min (erase f1) (vec_list v)) eqn:E.
        1: destruct s; inv H2.
        -- econstructor. eapply H. 1: lia. eauto.
        -- econstructor. congruence.
      * destruct eval eqn:E2; try congruence.
        destruct s; try congruence.
        destruct (eval n min (erase f2)) eqn:E3.
        1: destruct s; inv H2.
        -- econstructor. 1: eapply H. 1: lia. 1: eauto. eapply H. 1: lia. eauto.
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
        { eapply H1 with (f := ra_min f). 1: lia.
          destruct c0. 1: inv H3.
          econstructor. 1: lia.
          - intros ? ?. specialize (H10 j).
            assert (S c0 - (pos2nat j - n) = c0 - (pos2nat j - S n)) by lia.
            rewrite H6 in *.  eapply H10. lia.
          - assert (S c0 - (S n0 - n) = c0 - (S n0 - S n)) by lia. rewrite H5 in *.
            eassumption. }
        now rewrite H5.
    + intros.
      destruct n; try now inv H0. cbn in H0.
      destruct (eval n) eqn:E1; try now inv H0.
      destruct s; try congruence.
      destruct n1; inv H0.
      * econstructor. 1: lia.
        -- intros. pose proof (pos2nat_prop j). lia.
        -- eapply H. 1:lia. assert (n - (n0 - n0) = n) as -> by lia. eassumption.
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
              { rewrite H8 in H6. rewrite H3. eapply H6. lia. }
              assert (pos2nat j > min) by lia.
              eapply vec_pos_gt.
              rewrite pos2nat_nat2pos. lia.
        -- assert (S c0 - (n0 - min) = c0 - (n0 - S min)) by lia. rewrite H1. eassumption.
           Unshelve. exact vec_zero.
Qed.

Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.

Definition evalfun fuel c v := match eval fuel 0 c v with Some (inl x) => Some x | _ => None end.

From Undecidability Require Import MuRec_computable LVector.
From Undecidability.L.Util Require Import NaryApp ClosedLAdmissible.

Import L_Notations.

Definition cont_vec (k : nat) : term := lam (many_lam k (k (Vector.fold_right (fun n s => (ext (@cons nat) (var n)) s) (many_vars k)  (ext (@nil nat))))).

Lemma helper_closed k :
  bound k (Vector.fold_right (fun (n : nat) (s0 : term) => ext (@cons nat) n s0) (many_vars k) (ext (@nil nat))).
Proof.
  induction k.
  - cbn. cbv. repeat econstructor.
  - rewrite many_vars_S. cbn. econstructor. 1: econstructor. 1: eapply closed_dcl_x. 1: Lproc.
    1: econstructor; lia.
    eapply bound_ge. 1: eauto. lia.
Qed.

Lemma subst_closed s n u :
  closed s -> subst s n u = s.
Proof.
  now intros ->.
Qed.

Lemma vector_closed:
  forall (k : nat) (v : Vector.t nat k) (x : term), Vector.In x (Vector.map enc v) -> proc x.
Proof.
  intros k v.
  induction v; cbn; intros ? Hi. 1: inversion Hi. inv Hi. 1:Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. 1:subst; eauto. eapply nat_eq_dec.
Qed.

Lemma cont_vec_correct k s (v : Vector.t nat k) :
  proc s ->
  many_app (cont_vec k s) (Vector.map enc v) == s (enc v).
Proof.
  intros Hs.
  unfold cont_vec.
  rewrite equiv_many_app_L.
  2:{ eapply beta_red. 1:Lproc. rewrite subst_many_lam. replace (k + 0) with k by lia. reflexivity. }
  cbn -[plus mult]. rewrite Nat.eqb_refl.
  rewrite bound_closed_k. 2:eapply helper_closed.
  replace (3 * k) with (k + 2 * k) by lia.
  etransitivity.
  { apply many_beta. eapply vector_closed. }
  rewrite many_subst_app.
  rewrite many_subst_closed. 2:Lproc.
  replace (2 * k) with (2 * k + 0) by lia.
  eapply equiv_R.
  induction v.
  - cbn. reflexivity.
  - rewrite many_vars_S. cbn -[mult]. rewrite subst_closed; [ | now Lproc].
    rewrite Nat.eqb_refl.
    rewrite !many_subst_app.
    repeat (rewrite many_subst_closed; [ | now Lproc]).
    rewrite bound_closed_k. 2:eapply helper_closed. rewrite IHv.
    rewrite !enc_vector_eq.
    now Lsimpl.
Qed.

Definition mu_option : term := (lam (0 (mu (lam (1 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0))).

Lemma mu_option_proc : proc mu_option.
Proof.
  unfold mu_option. Lproc.
Qed.
#[export] Hint Resolve mu_option_proc : Lproc.

From Undecidability Require Import LOptions.

Lemma mu_option_equiv {X} `{encodable X} s (b : X)  :
  proc s ->
  mu_option s == s (mu (lam (s 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0).
Proof.
  unfold mu_option. intros Hs. now Lsimpl.
Qed.

Definition mu_option_spec {X} {ENC : encodable X} {I : encInj ENC} s (b : X)  :
  proc s ->
  (forall x : X, enc x <> lam 0) ->
 (forall n : nat, exists o : option X, s (enc n) == enc o) ->
  (forall b : X, forall m n : nat, s (enc n) == enc (Some b) -> m >= n -> s (enc m) == enc (Some b)) ->
  mu_option s == enc b <-> exists n : nat, s (enc n) == enc (Some b).
Proof.
  intros Hs Hinv Ht Hm.
  rewrite (@mu_option_equiv X); eauto.
  split.
  - intros He.
    match goal with [He : ?s == _ |- _ ] => assert (converges s) as Hc end.
    { eexists. split. 1: exact He. Lproc. }
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [_ Hc].
    destruct Hc as [v [Hc Hv]].
    pose proof (Hc' := Hc).
    eapply mu_sound in Hc as [n [-> [Hc1 _]]]; eauto.
    * exists n.
      destruct (Ht n) as [ [x | ] Htt].
      -- rewrite Htt. 
         enough (enc b == enc x) as -> % enc_extinj. 1: reflexivity.
         rewrite <- He.
         rewrite Hc'. Lsimpl. rewrite Htt. now Lsimpl.
      -- exfalso. eapply (Hinv b). eapply unique_normal_forms; try Lproc.
         rewrite <- He, Hc'. Lsimpl.
         rewrite Htt. Lsimpl. reflexivity.
    * Lproc.
    * intros n. destruct (Ht n) as [[] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
  - intros [n Hn].
    edestruct mu_complete' with (n := n) as [n' [H' H'']].
    4: rewrite H'.
    + Lproc.
    + intros m. destruct (Ht m) as [ [] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
    + Lsimpl. rewrite Hn. now Lsimpl.
    + destruct (Ht n') as [[] Heq]; rewrite Heq; Lsimpl.
      * enough (HH : enc (Some x) == enc (Some b))by now eapply enc_extinj in HH; inv HH.
        assert (n <= n' \/ n' <= n) as [Hl | Hl] by lia.
        -- eapply Hm in Hl; eauto. now rewrite <- Heq, Hl.
        -- eapply Hm in Hl; eauto. now rewrite <- Hn, Hl.
      * enough (false = true) by congruence.
        eapply enc_extinj. rewrite <- H''.
        symmetry. Lsimpl. rewrite Heq. now Lsimpl.
Qed.

#[export]
Instance computable_evalfun : computable evalfun.
Proof. extract. Qed.

Lemma vec_list_eq {n X} (v : Vector.t X n) :
  vec_list v = Vector.to_list v.
Proof.
  induction v; cbn; f_equal; eassumption.
Qed.  

Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.

Lemma eval_mono c min k (v : Vector.t nat k) (f : recalg k) o :
  eval c min (erase f) (vec_list v) = Some (inl o) -> forall c', c' >= c -> eval c' min (erase f) (vec_list v) = Some (inl o).
Proof.
  intros H c' Hl. eapply erase_correct in H.
  eapply ra_bs_mono in H. 2: eauto.
  now eapply erase_correct in H.
Qed.

Theorem computable_MuRec_to_L {k} (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R -> L_computable R.
Proof.
  intros [f Hf].
  exists (cont_vec k (lam (mu_option (lam (ext evalfun 0 (enc (erase f)) 1))))).
  intros v. rewrite <- many_app_eq_nat. split.
  - intros m. rewrite L_facts.eval_iff.
    assert (lambda (encNatL m)) as [b Hb]. { change  (lambda (enc m)). Lproc. }
    rewrite Hb. rewrite eproc_equiv. rewrite cont_vec_correct. 2: unfold mu_option; Lproc.
    assert (lam (mu_option (lam (ext evalfun 0 (enc (erase f)) 1))) (enc v) ==
          mu_option (lam (ext evalfun 0 (enc (erase f)) (enc v)))).
    {  unfold mu_option. now Lsimpl. }
    rewrite H. rewrite <- Hb.
    change (encNatL m) with (enc m).
    rewrite mu_option_spec. 2:Lproc.
    2:{ intros []; cbv; congruence. }
    2:{ intros. eexists. rewrite !enc_vector_eq. Lsimpl. reflexivity. }
    1: rewrite Hf.
    1: split.
    + intros [n Hn % erase_correct] % ra_bs_to_c. exists n.
      rewrite !enc_vector_eq. Lsimpl.
      unfold evalfun. rewrite <- vec_list_eq. now rewrite Hn.
    + intros [n Hn]. eapply ra_bs_from_c. eapply erase_correct with (c := n).
      match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
      { rewrite !enc_vector_eq. Lsimpl. subst t. reflexivity. } subst t.
      rewrite vec_list_eq. rewrite H0 in Hn. eapply enc_extinj in Hn.
      unfold evalfun in Hn. now destruct eval as [[] | ]; inv Hn.
    + intros. rewrite enc_vector_eq in *.
      match type of H0 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity. rewrite H2 in H0. clear H2.
      eapply enc_extinj in H0. Lsimpl.
      unfold evalfun in *.
      destruct (eval n) as [ [] | ] eqn:E; inv H0.
      rewrite <- vec_list_eq in *.
      eapply eval_mono in E. 1: rewrite E; eauto. lia.
  - intros v' [H1 H2] % eval_iff.
    eapply star_equiv_subrelation in H1.
    rewrite cont_vec_correct in H1. 2: unfold mu_option; Lproc.
    match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
    1: unfold mu_option. 1: Lsimpl. all: subst t. 1: reflexivity.
    rewrite H in H1.
    match type of H1 with ?s == _ => assert (converges s) end.
    1: exists v'; split; eassumption.
    eapply app_converges in H0 as [Hc _].
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [_ Hc].
    destruct Hc as [v'' [Hc1 Hc2]].
    pose proof (Hc1' := Hc1).
    eapply mu_sound in Hc1; eauto.
    + destruct Hc1 as [m [-> []]].
      rewrite Hc1' in H1.
      rewrite enc_vector_eq in H1.
      destruct (evalfun m (erase f) (Vector.to_list v)) eqn:E.
      * match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H4, E in H1.
      match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H5 in H1.
      eapply unique_normal_forms in H1. 2,3: Lproc.
      subst. exists n. reflexivity.
      * enough (true = false) by congruence. eapply enc_extinj.
        rewrite <- H0. rewrite enc_vector_eq. Lsimpl.
        now rewrite E.
    + Lproc.
    + intros n.
      destruct (evalfun n (erase f) (Vector.to_list v)) eqn:EE;
      eexists; rewrite enc_vector_eq; Lsimpl; rewrite EE; try Lsimpl; reflexivity.
Qed.

Definition UMUREC_HALTING c := exists fuel, evalfun fuel c nil <> None.

Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Lemma MUREC_red : recalg.MUREC_HALTING ⪯ UMUREC_HALTING.
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
  eapply reduces_transitive. 1:eapply MUREC_red.
  eapply L_recognisable_halt.
  exists (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).
  split.
  - econstructor. extract.
  - firstorder.
    + unfold evalfun in *. exists x0. destruct eval; try destruct s; try congruence.
    + exists x0. unfold evalfun in *. destruct eval; try destruct s; try congruence.
Qed.
