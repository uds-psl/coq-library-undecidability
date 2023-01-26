Require Import Arith Lia List Bool Eqdep_dec EqdepFacts.
From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat utils_list finite pos vec.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations ListAutomationFacts ListAutomationHints ListAutomationInstances.

Require Import Undecidability.MuRec.Util.recalg.

Section Enumerate.

  Definition match_n n {k} (l : list (recalg k)) : list (recalg n) := 
    match Nat.eq_dec k n with
      left Heq => match Heq in (_ = i) return list (recalg i) with eq_refl => l end
    | _ => nil end.

  Definition match_n_spec n l : @match_n n n l = l.
  Proof.
    unfold match_n. destruct (Nat.eq_dec n n) as [Heq|Hne]. 2:lia.
    unshelve eapply (@K_dec_type nat _ n (fun h => match h in (_ = i) return _ with eq_refl => l end = l)).
    1: apply Nat.eq_dec. easy.
  Qed.

  Fixpoint list_le n : list nat := match n with
    0 => 0 :: nil
  | S n => list_le n ++ [S n]
  end.

  Lemma list_le_spec n m : n el list_le m <-> n <= m.
  Proof.
    induction n as [|n IH] in m|-*.
    + split; try lia. intros _. induction m as [|m IH]. 1:now left. cbn. apply in_app_iff. now left.
    + split.
      - induction m as [|m IHm].
        * cbn. intros [|[]]; discriminate.
        * cbn. destruct (Nat.eq_dec n m) as [->|Hne]; try lia.
          intros [H1|H2]%in_app_iff. 1: specialize (IHm H1); lia.
          cbn in H2; lia.
      - induction m as [|m IHm].
        * intros H; lia.
        * intros H. cbn. apply in_app_iff. assert (n = m \/ n < m) as [->|Hr] by lia. 1: right; now left.
          left. apply IHm. lia.
  Qed.

  Fixpoint list_vectors X n (L:list X) : list (vec X n) :=
    match n as nn return list (vec X nn) with
      0 => Vector.nil X :: nil
    | S n => map (fun '(x,xr) => Vector.cons X x n xr) (L × list_vectors X n L)
    end.

  Lemma list_vectors_spec X n (L:list X) v : (forall (p:pos n), vec_pos v p el L) -> v el list_vectors X n L.
  Proof.
    induction v as [|x n xr IH].
    - intros _. cbn. now left.
    - intros H. cbn. eapply in_map_iff. exists (x,xr). split; try easy.
      apply in_prod. 1: apply (H pos0).
      apply IH. intros p. apply (H (Fin.FS p)).
  Qed.

  Fixpoint all_fins (n : nat) : list (Fin.t n) :=
      match n with
      | 0 => nil
      | S n => Fin.F1 :: map Fin.FS (all_fins n)
      end.

  Fixpoint L_recalg n f : list (recalg n) :=
    match f with
    | 0 => nil
    | S f => L_recalg n f
        ++ match_n n [ra_cst f] (* ra_cst *)
        ++ match_n n [ra_zero]  (* ra_zero *)
        ++ match_n n [ra_succ]  (* ra_succ *)
        ++ [@ra_proj n k | k ∈ all_fins n] (* ra_proj *)
        ++ match_n n (concat [concat [concat [  (* ra_comp *)
                      @ra_comp k n v1 v2::nil | v2 ∈ list_vectors _ k (L_recalg n f)]
                                              | v1 ∈ L_recalg k f]
                                              | k ∈ list_le f])
        ++ match n as k return list (recalg k) with 0 => nil | S k => (* ra_rec *)
                     (concat [concat [
                    @ra_rec k v1 v2::nil | v1 ∈ L_recalg k f]
                                         | v2 ∈ L_recalg (S (S k)) f]) end
        ++ match_n n (concat [ (* ra_min *)
                      @ra_min n v::nil | v ∈ L_recalg (S n) f])
    end.

  Lemma L_recalg_cml n :
    cumulative (L_recalg n).
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Ltac walklist n := let rec f m := try (apply in_app_iff; match m with 0 =>  left | S ?m => right; f m end) in
                     cbn -[app]; f n.

  Lemma exists_max k (P : pos k -> nat -> Prop) : 
        (forall (p:pos k), exists n, P p n) 
        -> exists m, forall (p:pos k), exists n, P p n /\ m >= n.
  Proof.
    intros H. induction k as [|k IH].
    - exists 0. intros p. now eapply pos_O_invert.
    - specialize (IH (fun p n => P (pos_nxt p) n)). cbn in IH.
      destruct IH as [m1 Hm1].
      + intros p. apply H.
      + destruct (H pos0) as [m2 Hm2].
        exists (max m1 m2).
        apply pos_S_invert.
        * exists m2. split; now try lia.
        * intros p. edestruct Hm1 as [m3 [Hm3A Hm3B]]. exists m3; split; try lia. exact Hm3A.
  Qed.

  Definition max3 a b c := max a (max b c).

  Lemma enum_recalg n:
    list_enumerator__T (L_recalg n) (recalg n).
  Proof.
    intros t. induction t as [k| | |k p|k i t gj [m1 IHt] IHgj|k t1 t2 [m1 IH1] [m2 IH2]|k t [m IHt]] using recalg_rect.
    - exists (S k). walklist 1. easy.
    - exists 1. walklist 2. easy.
    - exists 1. walklist 3. easy.
    - exists 1. walklist 4. apply in_map.
      induction p; cbn. 1: now left. right. now apply in_map.
    - destruct (exists_max _ _ IHgj) as [m2 Hm2].
      exists (S (max3 k m1 m2)). walklist 5. rewrite match_n_spec.
      eapply in_concat. exists (concat [concat [@ra_comp k i v1 v2 :: nil | v2 ∈ list_vectors _ k (L_recalg i (max3 k m1 m2))] | v1 ∈ L_recalg k (max3 k m1 m2)]).
      split.
      1: { apply in_map_iff. exists k. split; try easy. apply list_le_spec. unfold max3. lia. }
      eapply in_concat. exists (concat [@ra_comp k i t v2 :: nil| v2 ∈ list_vectors _ k (L_recalg i (max3 k m1 m2))]).
      split.
      1: { apply in_map_iff. exists t. split; try easy. eapply cum_ge'. 1: apply L_recalg_cml. 1: apply IHt. unfold max3; lia. }
      eapply in_concat. exists [@ra_comp k i t gj]. split.
      + eapply in_map_iff. exists gj; split; try easy.
        eapply list_vectors_spec. intros p. destruct (Hm2 p) as [idx [Hidx Hmidx]]. eapply cum_ge'. 1: apply L_recalg_cml.
        1: apply Hidx. unfold max3; lia.
      + now left.
    - exists (S (max m1 m2)). walklist 6.
      eapply in_concat. eexists (concat [ra_rec v1 t2::nil | v1 ∈ L_recalg k (max m1 m2)]). split.
      1: { apply in_map_iff. exists t2. split; try easy. eapply cum_ge'. 1: apply L_recalg_cml. 1: apply IH2. lia. }
      eapply in_concat. eexists (ra_rec t1 t2::nil). split. 2: now left.
      eapply in_map_iff. exists t1. split; try easy. eapply cum_ge'. 1: apply L_recalg_cml. 1: apply IH1. lia.
    - exists (S m). walklist 7. rewrite match_n_spec.
      eapply in_concat. eexists [_]. split. 2: now left.
      eapply in_map_iff. exists t. split. 1:easy. apply IHt.
  Qed.

  Lemma enumT_recalg n :
    enumerable__T (recalg n).
  Proof.
    apply enum_enumT. exists (L_recalg n). apply enum_recalg.
  Qed.
  Lemma enumeratorT_recalg n :
    {f & enumerator__T f (recalg n) }.
  Proof.
    eexists. eapply enumerator__T_to_list.
    apply enum_recalg.
  Defined.
End Enumerate.
