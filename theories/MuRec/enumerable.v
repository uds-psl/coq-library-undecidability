Require Import Arith Lia List Bool Eqdep_dec EqdepFacts.
From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat utils_list finite pos vec.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors.
Import ListAutomationNotations.

Require Import Undecidability.MuRec.recalg.

Definition C {n1 n2} (Heq:n1=n2) (alg:recalg n1) := (match Heq in (_ = x) return recalg x with eq_refl => alg end).

Lemma CE n H a : @C n n H a = a.
Proof.
  unshelve eapply (@K_dec_type nat _ n (fun h => C h a = a)). 2:easy.
  decide equality.
Qed.

Section EqDec.

  Definition recalg_inv_type := forall n (h : recalg n),
    {k & { H : 0 = n & h = C H (ra_cst k)}}
  + { H : 1 = n & h = C H (ra_zero)}
  + { H : 1 = n & h = C H (ra_succ)}
  + {k & {v & { H : k = n & h = C H (@ra_proj k v)}}}
  + {k & {i & {rk & {ri & { H : i = n & h = C H (@ra_comp k i rk ri)}}}}}
  + {k & {rk & {rSk & { H : S k = n & h = C H (@ra_rec k rk rSk)}}}}
  + {k & {rSk & { H : k = n & h = C H (@ra_min k rSk)}}}.

  Definition recalg_inv : recalg_inv_type.
  Proof.
    intros n h. induction h as [k| | |k v| k i rk ri IHrk IHri| k rk rSk Hrk HrSk|k rSk HrSk].
    + do 6 left. exists k, eq_refl. easy.
    + do 5 left; right. exists eq_refl. easy.
    + do 4 left; right. exists eq_refl. easy.
    + do 3 left; right. exists k, v, eq_refl. easy.
    + do 2 left; right. exists k, i, rk, ri, eq_refl. easy.
    + do 1 left; right. exists k, rk, rSk, eq_refl. easy.
    + do 0 left; right. exists k, rSk, eq_refl. easy.
  Qed.

  #[local] Ltac iinversion H := destruct (@recalg_inv _ H) as [[[[[[(k' & Heq & HH)|(Heq & HH)]|(Heq & HH)]|(k'&v'&Heq & HH)]|(k'&i'&rk'&ri'&Heq & HH)]|(k'&rk'&rSk'&Heq & HH)]|(k'&rSk'&Heq & HH)]; try discriminate Heq; try rewrite ! CE in *; subst; cbn.

  #[local] Ltac eqdec dec := let Hcc := fresh "Hcc" in let Hdd := fresh "Hdd" in
                        destruct (dec) as [Hcc|Hcc]; [try subst|right; intros Hdd; injection Hdd; try congruence].

  Lemma vec_pos_eq_dec X k (v1 v2: vec X k) :
    (forall (p : pos k) (e : X), {vec_pos v1 p = e} + {vec_pos v1 p <> e})
    -> {v1 = v2} + {v1 <> v2}.
  Proof.
    intros Hdec.
    assert ({forall p : pos k, vec_pos v1 p = vec_pos v2 p} + {~forall p : pos k, vec_pos v1 p = vec_pos v2 p}) as Hdec2.
    - induction k in v1,v2,Hdec|-*.
      + left. intros p. now apply pos_O_invert.
      + destruct (Hdec Fin.F1 (vec_pos v2 Fin.F1)) as [Hl|Hr].
        2: {right. intros H. apply Hr, H. }
        destruct (IHk (vec_tail v1) (vec_tail v2)) as [Hl2|Hr2].
        * intros p e. destruct (Hdec (Fin.FS p) e).
          -- left. rewrite vec_pos_tail. easy.
          -- right. rewrite vec_pos_tail. easy.
        * left. apply pos_S_invert.
          -- easy.
          -- intros p. specialize (Hl2 p). now rewrite <- !vec_pos_tail.
        * right. intros Hcc. apply Hr2. intros p. specialize (Hcc (Fin.FS p)).
          rewrite ! vec_pos_tail. easy.
    - destruct Hdec2 as [Hl|Hr].
      + left. apply vec_pos_ext. easy.
      + right. intros H. apply Hr. congruence.
  Qed.

  Definition recalg_dec n : eq_dec (recalg n).
  Proof.
    intros h1 h2. unfold dec. 
    induction h1 in h2|-*; iinversion h2; try (right; discriminate).
    (*ra_cst*)
    + eqdec (Nat.eq_dec n k'). now left.
    (*ra_zero*)
    + now left.
    + assert (k' = 0) as -> by lia. rewrite ! CE. right; discriminate.
    (*ra_succ*)
    + now left.
    + assert (k' = 0) as -> by lia. rewrite ! CE. right; discriminate.
    (* ra_proj *)
    + eqdec (@pos_eq_dec k p v'). 1: now left.
      intros H'%inj_pair2_eq_dec. 1:congruence. apply Nat.eq_dec.
    (* ra_comp *)
    + eqdec (Nat.eq_dec k k').
      eqdec (IHh1 rk').
      - eqdec (@vec_pos_eq_dec _ _ gj ri' H). 1: now left.
        intros H'%inj_pair2_eq_dec%inj_pair2_eq_dec. 2-3: apply Nat.eq_dec.
        now apply Hcc.
      - intros H'%inj_pair2_eq_dec%inj_pair2_eq_dec. 1: intros H2%inj_pair2_eq_dec. 2-4: apply Nat.eq_dec.
        now apply Hcc.
    (* ra_rec *)
    + assert (k = 0) as -> by lia. rewrite ! CE. right; discriminate.
    + assert (k = 0) as -> by lia. rewrite ! CE. right; discriminate.
    + destruct (Nat.eq_dec k k') as [->|Hcc].
      2: lia.
      rewrite ! CE.
      eqdec (IHh1_1 rk').
      2: {intros H1%inj_pair2_eq_dec. 1: intros H2%inj_pair2_eq_dec. 2-3: apply Nat.eq_dec. congruence. }
      eqdec (IHh1_2 rSk').
      2: {intros H1%inj_pair2_eq_dec. 2: apply Nat.eq_dec. congruence. }
      now left.
    (* ra_min *)
    + eqdec (IHh1 rSk').
      2: {intros H1%inj_pair2_eq_dec. 2: apply Nat.eq_dec. congruence. }
      now left.
  Qed.

  #[global] Existing Instance recalg_dec.

End EqDec.

Section Enumerate.

  Definition match_n n {k} (l : list (recalg k)) : list (recalg n) := 
    match Nat.eq_dec k n with
      left Heq => match Heq in (_ = i) return list (recalg i) with eq_refl => l end
    | _ => nil end.

  Definition match_n_spec n l : @match_n n n l = l.
  Proof.
    unfold match_n. destruct (Nat.eq_dec n n) as [Heq|Hne]. 2:lia.
    unshelve eapply (@K_dec_type nat _ n (fun h => match h in (_ = i) return _ with eq_refl => l end = l)). 1: apply Nat.eq_dec. easy.
  Qed.

  Fixpoint list_le n : list nat := match n with
    0 => [0]
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
      0 => [Vector.nil X]
    | S n => [Vector.cons X x n xr | (x,xr) ∈ (L × list_vectors n L)]
    end.

  Lemma list_vectors_spec X n (L:list X) v : (forall (p:pos n), vec_pos v p el L) -> v el list_vectors n L.
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
    | 0 => []
    | S f => L_recalg n f
        ++ match_n n [ra_cst f] (* ra_cst *)
        ++ match_n n [ra_zero]  (* ra_zero *)
        ++ match_n n [ra_succ]  (* ra_succ *)
        ++ [@ra_proj n k | k ∈ all_fins n] (* ra_proj *)
        ++ match_n n (concat [concat [concat [  (* ra_comp *)
                      [@ra_comp k n v1 v2] | v2 ∈ list_vectors k (L_recalg n f)]
                                           | v1 ∈ L_recalg k f]
                                           | k ∈ list_le f])
        ++ match n as k return list (recalg k) with 0 => [] | S k => (* ra_rec *)
                     (concat [concat [
                    [@ra_rec k v1 v2] | v1 ∈ L_recalg k f]
                                      | v2 ∈ L_recalg (S (S k)) f]) end
        ++ match_n n (concat [ (* ra_min *)
                      [@ra_min n v] | v ∈ L_recalg (S n) f])
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
    - destruct (exists_max IHgj) as [m2 Hm2].
      exists (S (max3 k m1 m2)). walklist 5. rewrite match_n_spec.
      eapply in_concat. exists (concat [concat [[@ra_comp k i v1 v2] | v2 ∈ list_vectors k (L_recalg i (max3 k m1 m2))] | v1 ∈ L_recalg k (max3 k m1 m2)]).
      split.
      1: { apply in_map_iff. exists k. split; try easy. apply list_le_spec. unfold max3. lia. }
      eapply in_concat. exists (concat [[@ra_comp k i t v2] | v2 ∈ list_vectors k (L_recalg i (max3 k m1 m2))]).
      split.
      1: { apply in_map_iff. exists t. split; try easy. eapply cum_ge'. 1: apply L_recalg_cml. 1: apply IHt. unfold max3; lia. }
      eapply in_concat. exists [@ra_comp k i t gj]. split.
      + eapply in_map_iff. exists gj; split; try easy.
        eapply list_vectors_spec. intros p. destruct (Hm2 p) as [idx [Hidx Hmidx]]. eapply cum_ge'. 1: apply L_recalg_cml.
        1: apply Hidx. unfold max3; lia.
      + now left.
    - exists (S (max m1 m2)). walklist 6.
      eapply in_concat. eexists (concat [[ra_rec v1 t2] | v1 ∈ L_recalg k (max m1 m2)]). split.
      1: { apply in_map_iff. exists t2. split; try easy. eapply cum_ge'. 1: apply L_recalg_cml. 1: apply IH2. lia. }
      eapply in_concat. eexists ([ra_rec t1 t2]). split. 2: now left.
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
