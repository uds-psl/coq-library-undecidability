From Undecidability.H10 Require Import H10 dio_single dio_logic.
From Undecidability.L.Datatypes Require Import LNat Lists LOptions LSum.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.



(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared Require Import DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import recalg.

Set Implicit Arguments.

Reserved Notation "  '[' f ';' v ']' '~~>' x " (at level 70).

(* Bigstep semantics for recursive algorithms *)
   
Inductive ra_bs : forall k, recalg k -> vec nat k -> nat -> Prop :=
    | in_ra_bs_cst  : forall n v,             [ra_cst n;        v] ~~> n
    | in_ra_bs_zero : forall v,               [ra_zero;         v] ~~> 0
    | in_ra_bs_succ : forall v,               [ra_succ;         v] ~~> S (vec_head v)
    | in_ra_bs_proj : forall k v j,           [@ra_proj k j;    v] ~~> vec_pos v j
    
    | in_ra_bs_comp : forall k i f (gj : vec (recalg i) k) v w x,
                                   (forall j, [vec_pos gj j;    v] ~~> vec_pos w j)
                               ->             [f;               w] ~~> x
                               ->             [ra_comp f gj;    v] ~~> x

    | in_ra_bs_rec_0 : forall k f (g : recalg (S (S k))) v x,
                                              [f;               v] ~~> x
                               ->             [ra_rec f g;   0##v] ~~> x

    | in_ra_bs_rec_S : forall k f (g : recalg (S (S k))) v n x y,
                                              [ra_rec f g;   n##v] ~~> x
                               ->             [g;         n##x##v] ~~> y
                               ->             [ra_rec f g; S n##v] ~~> y
                               
    | in_ra_bs_min : forall k (f : recalg (S k)) v x w ,
                           (forall j : pos x, [f;    pos2nat j##v] ~~> S (vec_pos w j))
                               ->             [f;            x##v] ~~> 0
                               ->             [ra_min f;        v] ~~> x
where " [ f ; v ] ~~> x " := (@ra_bs _ f v x).


Reserved Notation "  '[' f ';' v ';' c ']' '~~>' x " (at level 70).

(* Bigstep semantics for recursive algorithms *)
   
Inductive ra_bs_c : nat -> forall k, recalg k -> vec nat k -> nat -> Prop := 
    | in_ra_bs_c_cst  : forall c n v,             [ra_cst n;        v; S c] ~~> n
    | in_ra_bs_c_zero : forall c v,               [ra_zero;         v; S c] ~~> 0
    | in_ra_bs_c_succ : forall c v,               [ra_succ;         v; S c] ~~> S (vec_head v)
    | in_ra_bs_c_proj : forall c k v j,           [@ra_proj k j;    v; S c] ~~> vec_pos v j 
    
    | in_ra_bs_c_comp : forall c k i f (gj : vec (recalg i) k) v w x,
                                         (forall j, [vec_pos gj j;    v; c + k - pos2nat j] ~~> vec_pos w j)
                                 ->             [f;               w; c] ~~> x
                                 ->             [ra_comp f gj;    v; S c + 1 + k] ~~> x

    | in_ra_bs_c_rec_0 : forall c k f (g : recalg (S (S k))) v x,    
                                               [f;               v; c] ~~> x 
                                 ->             [ra_rec f g;   0##v; S c] ~~> x

    | in_ra_bs_c_rec_S : forall c k f (g : recalg (S (S k))) v n x y,          
                                              [ra_rec f g;   n##v; c] ~~> x
                               ->             [g;         n##x##v; c] ~~> y
                               ->             [ra_rec f g; S n##v; S c] ~~> y
                               
    | in_ra_bs_c_min : forall c k (f : recalg (S k)) v x w , 
                           (forall j : pos x, [f;    pos2nat j##v; c - pos2nat j] ~~> S (vec_pos w j)) 
                               ->             [f;            x##v; c] ~~> 0
                               ->             [ra_min f;        v; S c] ~~> x
where " [ f ; v ; c ] ~~> x " := (@ra_bs_c c _ f v x).

Lemma ra_bs_mono k (f : recalg k) v c1 x :
  [f ; v ; c1 ] ~~> x -> forall c2, c1 <= c2 -> [f ; v ; c2] ~~> x. 
Proof.
  induction 1; intros; try (destruct c2;[ omega | ]).
  - econstructor.
  - econstructor.
  - econstructor.
  - econstructor.
  - assert (S c2 = S (c2 - k - 1) + 1 + k ) as -> by omega.
    econstructor.
    + intros. eapply H0. omega.
    + eapply IHra_bs_c. omega.
  - econstructor. eapply IHra_bs_c. omega.
  - econstructor.
    + eapply IHra_bs_c1. omega.
    + eapply IHra_bs_c2. omega.
  - econstructor.
    + intros. eapply H0. omega.
    + eapply IHra_bs_c. omega.
Qed.

Require Import Equations.Prop.DepElim.

Lemma vec_sum_le:
  forall (k : nat) (cst : vec nat k) (j : pos k), vec_pos cst j <= vec_sum cst.
Proof.
  intros k cst j.
  induction cst; cbn.
  - inversion j.
  - depelim j. omega. specialize (IHcst j). omega.
Qed.

Lemma ra_bs_to_c k (f : recalg k) v x :
  [ f; v ] ~~> x -> exists c, [f ; v ; c ] ~~> x.
Proof.
  induction 1.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - exists 1. econstructor.
  - destruct IHra_bs as [c].
    eapply vec_reif in H0 as [cst].
    exists (1 + c + vec_sum cst + 1 + k). cbn.
    econstructor.
    + intros. eapply ra_bs_mono. eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); omega.
      enough (vec_pos cst j <= vec_sum cst).
      lia. eapply vec_sum_le.
    + eapply ra_bs_mono. eauto. omega.
  - destruct IHra_bs as [c]. exists (S c). now econstructor.
  - destruct IHra_bs1 as [c1].
    destruct IHra_bs2 as [c2].
    exists (1 + c1 + c2).
    cbn. econstructor.
    + eapply ra_bs_mono. eauto. omega.
    + eapply ra_bs_mono. eauto. omega.
  - destruct IHra_bs as [c].
    eapply vec_reif in H0 as [cst].
    exists (1 + c + vec_sum cst + x). cbn.
    econstructor. 
    + intros. eapply ra_bs_mono. eauto.
      rewrite <- Nat.add_sub_assoc.
      2: pose (pos2nat_prop j); omega.
      enough (vec_pos cst j <= vec_sum cst) by omega.
      eapply vec_sum_le.
    + eapply ra_bs_mono. eauto. omega.
Qed.

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

Run TemplateProgram (tmGenEncode "enc_reccode" reccode).
Hint Resolve enc_reccode_correct : Lrewrite.

Instance term_rc_comp: computable rc_comp. extract constructor. Qed.
Instance term_rc_cons : computable rc_cons.  extract constructor. Qed.
Instance term_rc_rec : computable rc_rec.  extract constructor. Qed.
Instance term_rc_min : computable rc_min.  extract constructor. Qed.

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

(* Lemma eval_mono_S fuel min c v r : *)
(*   eval fuel min c v = Some r -> eval (S fuel) min c v = Some r. *)
(* Proof. *)
(*   intros. induction fuel in H, c, min, r, v |- *. *)
(*   - inv H. *)
(*   - cbn in H. destruct c; eauto. *)
(*     + assert (IH2 := IHfuel min c2 v). *)
(*       destruct (eval fuel min c2 v); try congruence. *)
(*       destruct s; try congruence. *)
(*       assert (IH1 := IHfuel min c1 l). *)
(*       destruct (eval fuel min c1 l); try congruence. *)
(*       specialize (IH1 _ eq_refl). specialize (IH2 _ eq_refl). *)
(*       remember (S fuel) as n. cbn. *)
(*       rewrite IH2, IH1. eassumption. *)
(*     + assert (IH1 := IHfuel min c1 v). *)
(*       destruct (eval fuel min c1 v); try congruence. *)
(*       destruct s; try congruence. *)
(*       assert (IH2 := IHfuel min c2 v). *)
(*       destruct (eval fuel min c2 v); try congruence. *)
(*       destruct s; try congruence. inv H. *)
(*       specialize (IH1 _ eq_refl). specialize (IH2 _ eq_refl). *)
(*       remember (S fuel) as k. cbn. *)
(*       now rewrite IH2, IH1. *)
(*     + *)
(* Admitted. *)

(* Lemma eval_mono fuel1 fuel2 min c v r : *)
(*   eval fuel1 min c v = Some r -> fuel1 <= fuel2 -> eval fuel2 min c v = Some r. *)
(* Proof. *)
(*   intros. induction H0. *)
(*   - eauto. *)
(*   - eapply eval_mono_S. eauto. *)
(* Qed. *)

(* Inductive bigstep (min : nat) : reccode -> list nat -> nat -> Prop := *)
(* | sem_cst v n : bigstep min (rc_cst n) v n *)
(* | sem_zero v : bigstep min (rc_zero) v 0 *)
(* | sem_succ x v : bigstep min (rc_succ) (x :: v) (S x) *)
(* | sem_proj n v r : nth_error v n = Some r -> bigstep min (rc_proj n) v r *)
(* | sem_comp f g G v r : bigstep_list min g v G -> bigstep min f G r -> bigstep min (rc_comp f g) v r *)
(* | sem_rec1 f g v r : bigstep min f v r -> bigstep min (rc_rec f g) (0 :: v) r *)
(* | sem_rec2 f g n v y x : bigstep min (rc_rec f g) (n :: v) y -> bigstep min g (n :: y :: v) x -> bigstep min (rc_rec f g) (S n :: v) x *)
(* | sem_min f x v w : min <= x -> |w| >= x -> bigstep 0 f (x :: v) 0 -> (forall p n, min <= p < x -> nth_error w p = Some n -> bigstep 0 f (p :: v) (S n)) -> bigstep min (rc_min f) v x *)
(* with bigstep_list (min : nat) : reccode -> list nat -> list nat -> Prop := *)
(* | sem_cons f g v r G : bigstep min f v r -> bigstep_list min g v G -> bigstep_list min (rc_cons f g) v (r :: G) *)
(* | sem_nil v : bigstep_list min (rc_nil) v nil. *)

Inductive bigstep (min : nat) : nat -> reccode -> list nat -> nat -> Prop :=
| sem_cst c v n : bigstep min (S c) (rc_cst n) v n
| sem_zero c v : bigstep min (S c) (rc_zero) v 0
| sem_succ c x v : bigstep min (S c) (rc_succ) (x :: v) (S x)
| sem_proj c n v r : nth_error v n = Some r -> bigstep min (S c) (rc_proj n) v r
| sem_comp c f g G v r : bigstep_list min c g v G -> bigstep min c f G r -> bigstep min (S c) (rc_comp f g) v r
| sem_rec1 c f g v r : bigstep min c f v r -> bigstep min (S c) (rc_rec f g) (0 :: v) r
| sem_rec2 c f g n v y x : bigstep min c (rc_rec f g) (n :: v) y -> bigstep min c g (n :: y :: v) x -> bigstep min (S c) (rc_rec f g) (S n :: v) x
| sem_min c f x v w : min <= x -> |w| >= x -> bigstep 0 c f (x :: v) 0 -> (forall p n, min <= p < x -> nth_error w p = Some n -> bigstep 0 (c + x - p) f (p :: v) (S n)) -> bigstep min (c + x - min) (rc_min f) v x
with bigstep_list (min : nat) : nat -> reccode -> list nat -> list nat -> Prop :=
| sem_cons c f g v r G : bigstep min c f v r -> bigstep_list min c g v G -> bigstep_list min (S c) (rc_cons f g) v (r :: G)
| sem_nil c v : bigstep_list min c (rc_nil) v nil.

Definition rec_erase i (erase : forall i, recalg i -> reccode) := (fix rec k (v : vec (recalg i) k) := match v with vec_nil => rc_nil | vec_cons _ x v => rc_cons (erase _ x) (rec _ v) end).

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
  - cbn. inversion p.
  - cbn. depelim p.
    + reflexivity.
    + eapply IHv.
Qed.

Lemma erase_correct k (f : recalg k) v n c  :
  (ra_bs_c c f v n <-> eval c 0 (erase f) (vec_list v) = Some (inl n)).
  (* (forall i (g : vec (recalg i) k) w v', (forall j : pos k, [vec_pos g j; v'; c - pos2nat j ] ~~> vec_pos w j) <-> eval c 0 (rec_erase erase g) (vec_list v') = Some (inr (vec_list w))). *)
Proof.
  revert all except c.
  pattern c. eapply lt_wf_ind. intros.
  destruct f; cbn. 
  - split.
    + inversion 1. subst.
      eapply EqDec.inj_right_pair in H3. subst.
      reflexivity.
    + destruct n; inversion 1. subst. econstructor.
  - split.
    + inversion 1. subst.
      eapply EqDec.inj_right_pair in H2. subst.
      reflexivity.
    + destruct n; inversion 1. subst. econstructor.
  - split.
    + inversion 1. subst.
      eapply EqDec.inj_right_pair in H2. subst.
      cbn. depelim v. cbn. reflexivity.
    + destruct n; inversion 1. depelim v. subst. cbn in H2. inv H2. econstructor.
  - split.
    + inversion 1. subst.
      eapply EqDec.inj_right_pair in H4. subst.
      eapply EqDec.inj_right_pair in H5. subst.
      cbn. rewrite vec_list_nth. reflexivity.
    + destruct n; inversion 1. rewrite vec_list_nth in H2. inv H2. econstructor.
  - split.
    + inversion 1. subst.
      eapply EqDec.inj_right_pair in H2. subst.
      eapply EqDec.inj_right_pair in H7. subst.
      eapply EqDec.inj_right_pair in H6. subst.
      eapply EqDec.inj_right_pair in H6. subst.
      assert (forall j : pos k, eval (c0 + k - pos2nat j) 0 (erase (vec_pos v0 j)) (vec_list v) = Some (inl (vec_pos w j))).
      intros. eapply H. omega.
                                      
      cbn. eapply H in H9. 2:omega. eauto.
      eapply H in H9. 2:omega. cbn.

      assert (eval (c0 + 1 + k) 0 (rec_erase erase v0) (vec_list v) = Some (inr (vec_list w))).
      { clear - H1. induction v0.
        - cbn. assert (c0 + 1 + 0 = S c0) as -> by omega. cbn. depelim w. reflexivity.
        - cbn. assert (c0 + 1 + S n = S c0 + 1 + n) as -> by omega.
          cbn. pose proof (H1 pos_fst). cbn in H. rewrite pos2nat_fst in H.
          assert (c0 + S n - 0 = c0 + 1 + n) by omega. rewrite H0 in *. clear H0.
          rewrite H. depelim w. erewrite IHv0.  reflexivity.
          intros. specialize (H1 (pos_nxt j)). rewrite pos2nat_nxt in H1.
          assert (c0 + n - pos2nat j = c0 + S n - S (pos2nat j)) as -> by omega.
          rewrite H1. reflexivity.
      }
      rewrite H2. admit.
    + 


      edestruct H with (m := c0) as [_ ]. omega.
      eapply H1 in H8. clear H1. rewrite H8, H9. reflexivity.
    + destruct n; inversion 1.
      destruct (eval n 0 (rec_erase erase v0) (vec_list v)) eqn:E; try congruence.
      destruct s; try congruence.
      destruct (eval n 0 (erase f) l) eqn:E2; try congruence.
      destruct s; try congruence.
      inv H2.
      destruct (list_vec l). rewrite <- e in *. clear e.
      econstructor.
      * edestruct H with (m := n) as [_ ].
        omega.
        specialize (H1 i v0 x).

      * eapply H. omega. 


Lemma erase_correct k (f : recalg k) v n c :
  ra_bs_c c f v n <-> bigstep 0 c (erase f) (vec_list v) n.
Proof.
  revert k f v n.
  pattern c. eapply lt_wf_ind. intros.
  destruct f.
  - split; inversion 1; econstructor.
  - split; inversion 1; econstructor.
  - split.
    + intros. inversion H0. subst.
      eapply EqDec.inj_right_pair in H2. subst.
      depelim v. econstructor.
    + intros. inversion H0. subst.
      depelim v. cbn in H2. inv H2. econstructor.
  - split.
    + intros. inversion H0. subst.
      eapply EqDec.inj_right_pair in H4. subst.
      eapply EqDec.inj_right_pair in H5. subst.
      econstructor. clear. eapply vec_list_nth.              
    + intros. inversion H0. subst.
      rewrite vec_list_nth in H3. inv H3. econstructor.
  - split.
    + intros. cbn.
      admit.
    + admit.
  - split.
    + intros. inversion H0. subst.
      * eapply EqDec.inj_right_pair in H3. subst.
        eapply EqDec.inj_right_pair in H5. subst.
        eapply EqDec.inj_right_pair in H6. subst.
        cbn. econstructor. eapply H. omega. eauto.
      * eapply EqDec.inj_right_pair in H2. subst.
        eapply EqDec.inj_right_pair in H5. subst.
        eapply EqDec.inj_right_pair in H4. subst.
        cbn. econstructor.
        -- eapply H with (f := ra_rec f1 f2) (v := vec_cons n1 v0). omega. eauto. 
        -- eapply H with (v := vec_cons n1 (vec_cons x v0)). omega. eauto. 
    + intros. inversion H0; subst.
      * depelim v. inv H5. econstructor. eapply H. omega. eauto.
      * depelim v. inv H4. econstructor. eapply H. omega. eauto.
        eapply H. omega. eauto.
  - split.
    + 


  split.
  - intros. induction H.
    + econstructor.
    + econstructor.
    + depelim v. depelim v. cbn. econstructor.
    + econstructor.      
      depind v; cbn.
      * depelim j.
      * depelim j.
        -- rewrite pos2nat_fst. reflexivity.
        -- rewrite pos2nat_nxt. cbn. eauto.
    + admit.
    + econstructor. eauto.
    + econstructor. eauto. eauto.
    + eapply sem_min with (w := vec_list w).
      * omega.
      * rewrite vec_list_length. omega.
      * eauto. 
      * intros. admit.
  - 


Import ListNotations.

Fixpoint update X (l : list X) n x :=
  match n, l with
  | 0, _ :: l => x :: l
  | S n, y :: l => y :: update l n x
  | _, [] => []
  end.

Lemma eval_bigstep fuel min c v r :
  eval fuel min c v = Some r ->
  match r with
  | inl n => bigstep min fuel c v n
  | inr L => bigstep_list min fuel c v L
  end.
Proof.
  revert min c v r. induction fuel; cbn; intros; try destruct c; try congruence.
  all: try now (inv H; econstructor).
  - destruct v; inv H. econstructor.
  - destruct (nth_error v n) eqn:E; inv H. now econstructor.
  - assert (IH2 := IHfuel min c2 v).
    destruct (eval fuel min c2 v). destruct s. all:try congruence.
    assert (IH1 := IHfuel min c1 l).
    destruct (eval fuel min c1 l). destruct s. all:try congruence.
    specialize (IH1 _ eq_refl). specialize (IH2 _ eq_refl). inv H. cbn in *.
    econstructor. eauto. eauto.
  - assert (IH1 := IHfuel min c1 v).
    destruct (eval fuel min c1 v). destruct s. all:try congruence.
    assert (IH2 := IHfuel min c2 v).
    destruct (eval fuel min c2 v). destruct s. all:try congruence.
    specialize (IH1 _ eq_refl). specialize (IH2 _ eq_refl). inv H. cbn in *.
    econstructor. eauto. eauto.
  - destruct v; try congruence.
    destruct n.
    + assert (IH1 := IHfuel min c1 v).
      destruct (eval fuel min c1 v). destruct s. all:try congruence. inv H.
      specialize (IH1 _ eq_refl). cbn in *.
      econstructor. eauto.
    + assert (IH2 := IHfuel min (rc_rec c1 c2) (n :: v)).
      destruct (eval fuel min (rc_rec c1 c2) (n :: v)). destruct s. all:try congruence.
      specialize (IH2 _ eq_refl).
      assert (IH3 := IHfuel min c2 (n :: n0 :: v)).
      destruct (eval fuel min c2 (n :: n0 :: v)). destruct s. all:try congruence. 
      specialize (IH3 _ eq_refl). cbn in *. inv H.
      econstructor. eauto. eauto.
  - assert (IH1 := IHfuel 0 c (min :: v)).
    destruct (eval fuel 0 c (min :: v)); try congruence.
    destruct s; try congruence.
    specialize (IH1 _ eq_refl).
    destruct n.
    + inv H. cbn in *. eapply sem_min with (w := repeat min min). eauto. eauto.
      rewrite repeat_length. omega. eauto.
      intros. omega. 
    + assert (IH2 := IHfuel (S min) (rc_min c) v).
      destruct (eval fuel (S min) (rc_min c) v); try congruence.
      destruct s; inv H.
      specialize (IH2 _ eq_refl). cbn in *. inversion IH2. subst.
      eapply sem_min with (w := update w min n).
      omega. admit. eauto. intros.
      decide (min = p).
      * subst. admit.
      * eapply H3. omega. admit.
Admitted.

Scheme bigstep1_ind := Induction for bigstep Sort Prop
  with bigstep2_ind := Induction for bigstep_list Sort Prop.
Combined Scheme bigstepInd from bigstep1_ind, bigstep2_ind.

Lemma bigstep_eval min  :
  (forall c v n, bigstep min c v n -> exists fuel, eval fuel min c v = Some (inl n)) /\
  (forall c v L, bigstep_list min c v L -> exists fuel, eval fuel min c v = Some (inr L)).
Proof.
  apply bigstepInd with (P := fun min c v n _ => exists fuel : nat, eval fuel min c v = Some (inl n)) (P0 := fun min c v L _ => exists fuel : nat, eval fuel min c v = Some (inr L)).
  all: cbn; intros.
  all: try now exists 1; eauto.
  - exists 1. cbn. now rewrite e. 
  - destruct H, H0.
    exists (1 + x + x0). 
    cbn. erewrite eval_mono; eauto.
    cbn. erewrite eval_mono; eauto.
    eauto. omega. omega.
  - destruct H.
    exists (1 + x). 
    cbn. erewrite eval_mono; eauto.
    eauto.
  - destruct H, H0.
    exists (1 + x0 + x1). 
    cbn. erewrite eval_mono; eauto.
    cbn. erewrite eval_mono; eauto.
    eauto. omega. omega.
  - destruct H.
    exists (1 + x0). 
    cbn. decide (min0 = x).
    + subst. now rewrite H.
    + assert (min0 <= min0 < x). omega. eapply H0 in H1 as [].
      admit. admit.
  - destruct H, H0.
    exists (1 + x0 + x). 
    cbn. erewrite eval_mono; eauto.
    cbn. erewrite eval_mono; eauto.
    eauto. omega. omega.
Admitted.

Instance term_eval : computable eval.
Proof.
  extract.
Qed.
