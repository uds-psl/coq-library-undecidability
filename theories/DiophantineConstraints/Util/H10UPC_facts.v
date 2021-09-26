(* 
  Autor(s):
    Andrej Dudenhefner (1) 
    Johannes Hostert (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import Arith Lia List.
From Undecidability.DiophantineConstraints Require Import H10UPC.
From Equations Require Import Equations.
Set Equations With UIP.

(** Utils for H10UPC *)

(** This section contains useful functions and lemmas for proofs later on. *)
Section Utils.

  (** In the relation h10upc_sem_direct ((a,b),(c,d)), d is a function of b. *)
  Definition c2_full (x:nat) : {y:nat | x * S x = y+y}.
  Proof. 
    induction x as [|x [y' IH]].
    - exists 0. lia.
    - exists (y'+x+1). nia.
  Defined.

  Definition c2 (x:nat) := match (c2_full x) with exist _ y _ => y end.

  Definition c2_descr (x:nat) : x * S x = c2 x + c2 x.
  Proof.
  unfold c2. now destruct (c2_full x).
  Qed. 

  (** Direct semantics of h10upc_sem *)
  Definition h10upc_sem_direct (c : h10upc) :=
    match c with 
      | ((x, y), (z1, z2)) => 
          1 + x + y = z1 /\ y * (1 + y) = z2 + z2
    end.

  (** Inversion lemma for h10upc_sem_direct (basically axiom 2) *)
  Lemma h10upc_inv (a b c d : nat) : h10upc_sem_direct ((a,S b),(c,d)) -> 
           {c':nat & {d':nat & h10upc_sem_direct ((a,b),(c',d')) 
                               /\ S c' = c /\ d' + b + 1 = d}}.
  Proof.
  intros [Hl Hr].
  exists (a + S b). exists (c2 b).
  repeat split.
  - lia.
  - apply c2_descr.
  - lia.
  - enough (2*(c2 b + b + 1) = d+d) by nia. rewrite <- Hr.
    cbn. rewrite Nat.mul_comm. cbn. symmetry.
    pose (c2_descr b) as Hb. nia.
  Qed.

  (** h10upc_sem_direct is irreflexive *)
  Lemma h10_rel_irref (p:nat*nat) : ~ (h10upc_sem_direct (p,p)).
  Proof.
  intros H. destruct p as [a b]. cbn in H. lia.
  Qed.

  (** Utility function for finding the highest variable in a h10upc constraint *)
  Definition highest_var (x:h10upc) := match x with ((a,b),(c,d)) => Nat.max a (Nat.max b (Nat.max c d)) end.
  Lemma highest_var_descr (x:h10upc) : let hv := highest_var x in match x with ((a,b),(c,d)) => a <= hv /\ b <= hv /\ c <= hv /\ d <= hv end.
  Proof.
  destruct x as [[a b] [c d]]. cbn. repeat split; lia.
  Qed.

  (** Utility function for finding the highest variable in a h10upc constraint collection *)
  Fixpoint highest_var_list (x:list h10upc) := match x with nil => 0 | x::xr => Nat.max (highest_var x) (highest_var_list xr) end.
  Lemma highest_var_list_descr (x:list h10upc) (h:h10upc) : In h x ->  highest_var h <= highest_var_list x.
  Proof.
  induction x as [|hh x IH].
  - intros [].
  - intros [hhh|hx].
    + cbn. rewrite hhh. lia.
    + cbn. specialize (IH hx). lia.
  Qed.

  (** Utility function for finding the highest value in an environment, considering variables up to some n *)
  Fixpoint highest_num (env: nat -> nat) (n:nat) : nat := match n with 0 => env 0 | S n => Nat.max (env (S n)) (highest_num env n) end.
  Lemma highest_num_descr (env:nat -> nat) (n:nat) (m:nat) : m <= n -> env m <= highest_num env n.
  Proof.
  induction n as [|n IH].
  - intros Hm. assert (m=0) as Hm0. 1:lia. cbn. rewrite Hm0. lia.
  - intros HmSn. cbn. destruct (Nat.eq_dec (S n) m) as [Heq|Hneq].
    + rewrite <- Heq. lia.
    + assert (m <= n) as Hmn. 1:lia. specialize (IH Hmn). lia.
  Qed.

End Utils.

(** This section contains an alternative characterization of h10upc_sem_direct and some meta-theory.
    h10upc_sem_direct is the equational characterization of the H10UPC relation.
    h10upc_ind is presented as an alternative, inductive characterization of that relation. *)
Section InductiveCharacterization.

  (** Characterizing equations for h10upc_sem_direct *)

  Definition ax1 (P : (nat*nat)*(nat*nat) -> Prop) := forall a c, P ((a,0),(c,0)) <-> a + 1 = c.
  Definition ax2 (P : (nat*nat)*(nat*nat) -> Prop) := forall a b c d , (b <> 0 /\ P ((a,b),(c,d))) <->
               (exists b' c' d', P ((a,b'),(c',d')) /\ P ((d',b'),(d,d')) /\ P ((b',0),(b,0)) /\ P ((c',0),(c,0))).
  Definition ax2w (P : (nat*nat)*(nat*nat) -> Prop) := forall a b c d ,
               (exists b' c' d', P ((a,b'),(c',d')) /\ P ((d',b'),(d,d')) /\ P ((b',0),(b,0)) /\ P ((c',0),(c,0)))
               -> (P ((a,b),(c,d))).
  Definition ax3 (P : (nat*nat)*(nat*nat) -> Prop) := forall a c d, P ((a,0),(c,d)) -> d = 0.

  Definition sat P := ax1 P /\ ax2 P /\ ax3 P.
  Definition satw P := ax1 P /\ ax2w P.

  (** Inductive definition of h10upc_sem_direct *)
  Inductive h10upc_ind : (nat*nat)*(nat*nat) -> Prop :=
    base : forall a, h10upc_ind ((a,0),(S a,0))
  | step : forall a b c d b' c' d', h10upc_ind ((a,b'),(c',d'))
                                 -> h10upc_ind ((d',b'),(d,d'))
                                 -> h10upc_ind ((b',0),(b,0))
                                 -> h10upc_ind ((c',0),(c,0))
                                 -> h10upc_ind ((a,b),(c,d)).
  Derive Signature for h10upc_ind.

  (** Prove that h10upc_ind and h10upc_sem_direct are equivalent. *)
  (** First step: Show that there is no k < 0, since h10upc_ind is inductive. *)
  Lemma h10upc_ind_not_less_0 : forall k, h10upc_ind ((k,0),(0,0)) -> False.
  Proof.
  refine (fix H n k {struct k} : False := _ ). depelim k. apply (H b' k3).
  Qed.


  (** Next step: show equivalence for the base case. *)
  Lemma base_equiv a c d : h10upc_sem_direct ((a,0),(c,d)) <-> h10upc_ind ((a,0),(c,d)).
  Proof. split.
  * intros [H1 H2]. assert (d=0) as -> by lia. assert (c = S a) as -> by lia. apply base.
  * intros H. depelim H.
    - cbn. lia.
    - exfalso. now eapply h10upc_ind_not_less_0 with b'.
  Qed.

  (** Last step: show equivalence for the "step" case. *)
  Lemma h10_equiv a b c d  : h10upc_sem_direct ((a,b),(c,d)) <-> h10upc_ind ((a,b),(c,d)).
  Proof. induction b as [|b IH] in a,c,d|-*.
  - apply base_equiv.
  - symmetry. split.
    * intros H. inversion H; subst.
      rewrite <- base_equiv in H6, H7. cbn in H6,H7.
      assert (b' = b) as -> by lia.
      assert (S c' = c) as <- by lia.
      rewrite <- IH in H4,H5. cbn in H4,H5. cbn. lia.
    * intros [H1 H2]. eapply step with b (c-1) (d-b-1).
      + rewrite <- IH. cbn; lia.
      + rewrite <- IH. cbn; lia.
      + rewrite <- base_equiv. cbn; lia.
      + rewrite <- base_equiv. cbn; lia.
  Qed.


  (** Show that h10upc_sem_direct satisfies the axioms. *)
  Lemma eqRelSat : sat h10upc_sem_direct.
  Proof.
  split. 2:split.
  - intros a c. cbn. lia.
  - intros a. intros. split.
    * intros [H1 [H2 H3]]. destruct b as [|b']. 1:easy.
      exists b', (c-1), (d-b'-1). repeat split.
      all: lia.
    * intros [b' [c' [d' [H1 [H2 [H3 H4]]]]]]. cbn in H1,H2,H3,H4. cbn; lia.
  - intros a c d. cbn. lia.
  Qed.


  (** If P fulfills the axioms, and Q fulfills the weak axioms, then P is stronger than Q. *)
  (** Again, first the base case: *)
  Lemma satEquiv0 P Q : sat P -> satw Q -> forall a c d, P ((a,0),(c,d)) -> Q ((a,0),(c,d)).
  Proof. intros [HP1 [HP2 HP3]] [HQ1 HQ2] a c d.
  intros H.
  * pose proof (HP3 a c d H) as k. rewrite k in *.
    rewrite (HP1 a c) in H. rewrite (HQ1 a c). easy.
  Qed.

  (** Then the step case: *)
  Lemma satEquiv P Q : sat P -> satw Q -> forall a b c d, P ((a,b),(c,d)) -> Q ((a,b),(c,d)).
  Proof. intros [HP1 [HP2 HP3]] [HQ1 HQ2] a b c d.
  induction b as [|b' IH] in a,c,d|-*.
  * apply satEquiv0; firstorder.
  * destruct (HP2 a (S b') c d) as [HP21 HP22].
    pose proof (HQ2 a (S b') c d) as HQ22.
    intros H.
    - apply HQ22. destruct HP21 as [b'' [c' [d' [H1 [H2 [H3 H4]]]]]].
      + split; easy.
      + exists b'', c', d'. unfold ax1 in HP1. rewrite HP1 in H3. assert (b'' = b') as -> by lia.
        unfold ax1 in HQ1. rewrite !HQ1. rewrite <- !HP1. rewrite <- HP1 in H3. split. 2:split. 3:tauto.
        all: apply IH; easy.
  Qed.

  (** Congruence lemma: equivalent P,Q fulfill the same axioms *)
  Lemma satCongr P Q : (forall a b c d, P ((a,b),(c,d)) <-> Q ((a,b),(c,d))) -> sat P -> sat Q.
  Proof.
  intros H [H1 [H2 H3]]. split. 2:split.
  - unfold ax1 in *. intros a c. rewrite <- H. apply H1.
  - unfold ax2 in *. intros a b c d. rewrite <- H. split.
    * destruct (H2 a b c d) as [H2' _]. intros H4.
      destruct (H2' H4) as [b' [c' [d' H5]]].
      exists b', c', d'. rewrite <- !H. apply H5.
    * destruct (H2 a b c d) as [_ H2']. intros [b' [c' [d' H4]]].
      apply H2'. exists b',c',d'. rewrite !H. apply H4.
  - unfold ax3 in *. intros a c d. rewrite <- H. apply H3.
  Qed.

  (** It follows that h10upc_ind also fulfills the axioms. *)
  Lemma indRelSat : sat h10upc_ind.
  Proof.
  eapply satCongr with h10upc_sem_direct.
  - intros a b c d. apply h10_equiv.
  - apply eqRelSat.
  Qed.

  (** The weak axioms are weaker. *)
  Lemma sat_satw P : sat P -> satw P.
  Proof.
  intros [H1 [H2 H3]]. split.
  * easy.
  * intros a b c d H. destruct (H2 a b c d) as [_ H2R]. now apply H2R.
  Qed.


End InductiveCharacterization.
