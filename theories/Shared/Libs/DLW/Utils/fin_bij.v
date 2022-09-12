(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac fin_base fin_choice.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

Set Implicit Arguments.

Definition bij_t (X Y : Type) := { i : X -> Y & { j | (forall x, j (i x) = x) /\ forall y, i (j y) = y } }.

Definition surj_t (X Y : Type) := { s : X -> Y | forall y, exists x, y = s x }.

Fact surj_t_compose X Y Z : surj_t X Y -> surj_t Y Z -> surj_t X Z.
Proof. 
  intros (f & Hf) (g & Hg); exists (fun x => g (f x)).
  intros z.
  destruct (Hg z) as (y & Hy).
  destruct (Hf y) as (x & Hx).
  exists x; subst; auto.
Qed.

Fact finite_t_surj_t X Y : surj_t X Y -> finite_t X -> finite_t Y.
Proof.
  intros [ s E ] (l & Hl).
  exists (map s l).
  intros y; rewrite in_map_iff. 
  destruct (E y) as (x & ?); exists x; auto. 
Qed.

Fact finite_t_pos_equiv X : (finite_t X -> { n : _ & surj_t (pos n) X })
                          * ({ n : _ & surj_t (pos n) X } -> finite_t X).
Proof.
  split.
  + intros (l & Hl).
    exists (length l).
    destruct (list_vec_full l) as (v & Hv).
    rewrite <- Hv in Hl.
    generalize (length l) v Hl.
    clear l v Hl Hv.
    intros n v H.
    exists (vec_pos v).
    intros x; apply (vec_list_inv _ _ (H x)).
  + intros (n & Hn).
    generalize (finite_t_pos n).
    apply finite_t_surj_t; auto.
Qed.

Fact NoDup_vec_list X n v : NoDup (@vec_list X n v) -> forall p q, vec_pos v p = vec_pos v q -> p = q.
Proof.
  induction v as [ | n x v IHv ]; intros H p q.
  + invert pos p.
  + simpl in H; rewrite NoDup_cons_iff in H.
    destruct H as [ H1 H2 ].
    invert pos p; invert pos q; intros E; auto.
    1,2: destruct H1; subst; apply in_vec_list, in_vec_pos.
    f_equal; apply IHv; auto.
Qed.

Section list_discr_vec.

  Variable (X : Type) (D : forall x y : X, { x = y } + { x <> y }).

  Fact vec_search n (v : vec X n) x : { p | x = vec_pos v p } + { ~ in_vec x v }.
  Proof.
    induction v as [ | y n v [ (p & ->) | H ] ].
    + right; simpl; auto.
    + left; exists (pos_nxt p); auto.
    + destruct (D y x).
      * left; exists pos0; auto.
      * right; contradict H; simpl in H; tauto.
  Qed.

  Variable (ll : list X).

  Let l := nodup D ll.
  Let Hl1 : NoDup l := NoDup_nodup D ll.
  Let Hl2 : forall x, In x l <-> In x ll := nodup_In D ll.

  Let v := proj1_sig (list_vec_full l).
  Let Hv : vec_list v = l := proj2_sig (list_vec_full l).

  Let f x := 
    match vec_search v x with
      | inleft (exist _ p Hp) => Some p
      | inright _             => None
    end. 

  Fact list_discr_pos_n :
         { n : nat & 
         { v : vec X n &
         { f : X -> option (pos n)  
         |  (forall x, in_vec x v <-> In x ll)
         /\ (forall x, In x ll <-> f x <> None) 
         /\ (forall p, f (vec_pos v p) = Some p)
         /\ (forall x p, f x = Some p -> vec_pos v p = x) } } }.
  Proof.
    exists (length l), v, f; msplit 3.
    + intro; rewrite in_vec_list, Hv; apply Hl2.
    + intros x; rewrite <- Hl2.
      rewrite <- Hv at 1.
      unfold f.
      destruct (vec_search v x) as [ (p & ->) | H ].
      * rewrite <- in_vec_list; split; try discriminate.
        intros _; apply in_vec_pos.
      * rewrite <- in_vec_list; tauto.
    + intros p; unfold f. 
      destruct (vec_search v (vec_pos v p)) as [ (q & Hq) | H ].
      * apply NoDup_vec_list in Hq; subst; auto.
        rewrite Hv; auto.
      * destruct H; apply in_vec_pos.
    + intros x p; unfold f.
      destruct (vec_search v x) as [ (q & ->) | H ].
      * inversion 1; auto.
      * discriminate.
  Qed.

End list_discr_vec.

Fact list_discrete_bij_pos X (l : list X) : 
        (forall x y : X, { x = y } + { x <> y })
     -> { n : nat & 
        { f : forall x, In x l -> pos n &
        { g : pos n -> X 
        |  (forall p, In (g p) l) 
        /\ (forall x Hx, g (f x Hx) = x)
        /\ (forall p H, f (g p) H = p) } } }.
Proof. 
  intros D.
  generalize (NoDup_nodup D l) (nodup_In D l).
  set (l' := nodup D l); intros H1 H2.
  revert H1 H2.
  generalize l'; clear l'; intros l' H1 H2.
  exists (length l').
  destruct (list_vec_full l') as (v & Hv).
  rewrite <- Hv in H1, H2.
  generalize (NoDup_vec_list _ H1); intros H3.
  destruct list_reif_t with (l := l) (R := fun x p => vec_pos v p = x)
    as (f & Hf).
  { intros x Hx; apply in_vec_dec_inv; auto.
    apply in_vec_list, H2; auto. }
  exists f, (vec_pos v); msplit 2; auto.
  intro; apply H2, in_vec_list, in_vec_pos.
Qed.

Fact list_discrete_bij_nat X (l : list X) : 
        (forall x y : X, { x = y } + { x <> y })
     -> { n : nat & 
        { f : X -> nat &
        { g : nat -> option X 
        |  (forall x, In x l -> f x < n)
        /\ (forall x, In x l -> g (f x) = Some x)
        /\ (forall p, p < n -> exists x, g p = Some x /\ f x = p) } } }.
Proof.
  intros D.
  destruct (list_discrete_bij_pos l D)
    as (n & f & g & H1 & H2 & H3).
  exists n.
  exists (fun x => match in_dec D x l with
    | left H => pos2nat (f x H)
    | right _ => 0
  end).
  exists (fun k => match le_lt_dec n k with
    | left _  => None
    | right H => Some (g (nat2pos H))
  end).
  msplit 2.
  + intros x H; destruct (in_dec D x l); try tauto; apply pos2nat_prop.
  + intros x H; destruct (in_dec D x l) as [ Hx | Hx ]; try tauto.
    destruct (le_lt_dec n (pos2nat (f x Hx))) as [ H' | H' ].
    * generalize (pos2nat_prop (f _ Hx)); lia.
    * f_equal; rewrite nat2pos_pos2nat; auto.
  + intros p Hp.
    exists (g (nat2pos Hp)); split.
    * destruct (le_lt_dec n p) as [ | ? ]; try (exfalso; lia).
      do 2 f_equal; apply pos2nat_inj.
      rewrite !pos2nat_nat2pos; auto.
    * destruct (in_dec D (g (nat2pos Hp)) l) as [ | [] ]; auto.
      rewrite H3, pos2nat_nat2pos; auto.
Qed.

Fact finite_t_discrete_bij_t_pos X : 
        finite_t X
     -> (forall x y : X, { x = y } + { x <> y })
     -> { n : nat & bij_t X (pos n) }.
Proof. 
  intros (l & Hl) D.
  destruct list_discrete_bij_pos with (l := l) (1 := D)
    as (n & f & g & H1 & H2 & H3).
  exists n, (fun x => f x (Hl x)), g; split; auto.
Qed.

