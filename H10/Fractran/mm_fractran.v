(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Permutation.

Import ListNotations.

Require Import utils_tac utils_list utils_nat gcd prime rel_iter pos vec.
Require Import sss subcode mm_defs mm_no_self.
Require Import fractran_defs prime_seq.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db. 

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I // s -1> t" := (mm_sss I s t).
Local Notation "P /MM/ s → t" := (sss_step (@mm_sss _) P s t) (at level 70, no associativity). 
Local Notation "P /MM/ s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).

Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).
Local Notation "l /F/ x -[ k ]-> y" := (fractran_steps l k x y) (at level 70, no associativity).

Set Implicit Arguments.

(* Fractran simulates MM *)

(*       let a MM program 1: INC ... k: DEC ... n: _ *)
(*       with variables x1...xm *)

(*    we use p1...pn,q1...qm distinct primes and  *)
(*    encode the state (i,v1,...,vm) *)
(*    as p1^0*...*pi^1*...*pn^0*q1^v1*...*qm^vm *)

(*    i: INC xu   ---> (qu*p(i+1) / pi) *)
(*    i: DEC xu j ---> (p(i+1) / pi*qu) and (pj / pi) (the second constraint should appear AFTER in the list) *)

Definition encode_state {n} (c : nat * vec nat n) := ps (fst c) * @exp n 0 (snd c).

Definition encode_inc n  i (u : pos n) := (ps (i + 1) * qs u, ps i).
Definition encode_dec n  i (u : pos n) (_ : nat) := (ps (i + 1), ps i * qs u).
Definition encode_dec2 n i (u : pos n) j := (ps j, ps i).

Fixpoint encode_mm_instr m i (l : list (mm_instr m)) : list (nat * nat) :=
  match l with
  | nil          => nil
  | INC u   :: l => encode_inc i u                        :: encode_mm_instr (S i) l
  | DEC u j :: l => encode_dec i u j :: encode_dec2 i u j :: encode_mm_instr (S i) l
  end.

Fact encode_mm_instr_app m i l r : @encode_mm_instr m i (l++r) = encode_mm_instr i l++encode_mm_instr (length l+i) r.
Proof.
  revert i; induction l as [ | [ u | u j ] l IHl ]; intros i; simpl; auto; f_equal;
    specialize (IHl (S i)); simpl in IHl; rewrite IHl; do 2 f_equal; [ | f_equal ]; omega.
Qed.

Fact encode_mm_instr_regular n i l : Forall (fun c => fst c <> 0 /\ snd c <> 0) (@encode_mm_instr n i l).
Proof.
  revert i; induction l as [ | [ u | u j ] l IHl ]; intros i; simpl.
  + constructor.
  + constructor; auto; unfold encode_inc; simpl; split;
      [ apply Nat.neq_mul_0; split | ]; apply prime_neq_0; apply nthprime_prime.
  + constructor; [ | constructor ]; auto; split; unfold encode_dec, encode_dec2; simpl.
    2: apply Nat.neq_mul_0; split.
    all: apply prime_neq_0; apply nthprime_prime.
Qed.

Fact encode_mm_instr_regular' n i l : fractran_regular (@encode_mm_instr n i l).
Proof.
  generalize (@encode_mm_instr_regular n i l); apply Forall_impl; tauto.
Qed.

Fact encode_mm_instr_in_inv n i P el c er : 
          @encode_mm_instr n i P = el++c::er
       -> exists l rho r, P = l++rho::r
                       /\ ( (exists u, rho = INC u 
                                    /\ c = encode_inc (length l+i) u 
                                    /\ el = encode_mm_instr i l
                                    /\ er = encode_mm_instr (S (length l)+i) r) 
                         \/ (exists u j, rho = DEC u j 
                                     /\ (c = encode_dec (length l+i) u j
                                      /\ el = encode_mm_instr i l
                                      /\ er = encode_dec2 (length l+i) u j::encode_mm_instr (S (length l)+i) r
                                      \/ c = encode_dec2 (length l+i) u j
                                      /\ el = encode_mm_instr i l++encode_dec (length l+i) u j::nil
                                      /\ er = encode_mm_instr (S (length l)+i) r)) ).
Proof.
  revert i el c er; induction P as [ | [ u | u j ] P IHP ]; simpl; intros i el c er H.
  + destruct el; discriminate.
  + Check list_cons_app_cons_eq_inv.
destruct list_cons_app_cons_eq_inv with (1 := H)
      as (-> & .

 destruct H as [ <- | H ].
    * exists nil, (INC u), P; split; auto; left; exists u; split; auto.
    * destruct IHP with (1 := H) as (l & rho & r & -> & H1).
      exists (INC u::l), rho, r; split; auto.
      destruct H1 as [ (v & -> & ->) | (v & j & -> & [ -> | -> ]) ].
      - left; exists v; split; auto; f_equal; simpl; omega.
      - right; exists v, j; split; auto; left; f_equal; simpl; omega.
      - right; exists v, j; split; auto; right; f_equal; simpl; omega.
  + destruct H as [ <- | [ <- | H ] ].
    1,2: exists nil, (DEC u j), P; split; auto; right; exists u, j; split; auto.
    destruct IHP with (1 := H) as (l & rho & r & -> & H1).
    exists (DEC u j::l), rho, r; split; auto.
    destruct H1 as [ (v & -> & ->) | (v & j' & -> & [ -> | -> ]) ].
    - left; exists v; split; auto; f_equal; simpl; omega.
    - right; exists v, j'; split; auto; left; f_equal;simpl; omega.
    - right; exists v, j'; split; auto; right; f_equal;simpl; omega.
Qed.

Local Notation divides_mult_inv := prime_div_mult.

Local Ltac inv H := inversion H; subst; clear H.

Opaque ps qs.

Lemma divides_encode_state i k n v : divides (ps i) (@encode_state n (k,v)) -> i = k.
Proof.
  unfold encode_state. intros. induction v.
  - cbn in H. replace (ps k * 1) with (ps k) in H by omega.
    now eapply primestream_divides in H.
  - cbn in H. eapply divides_mult_inv in H as [ | [ | ] % divides_mult_inv ]; eauto.
    + now eapply primestream_divides in H.
    + eapply divides_pow in H; eauto.
      now eapply ps_qs_div in H.
    + now eapply ps_exp in H.
Qed.

Lemma skip_steps m k l r k' (v v' : vec _ m) :
      @mm_no_self_loops m (k, l ++ r) 
   -> encode_mm_instr (k + length l) r /F/ encode_state (k + length l,v) → encode_state (k',v') 
   -> encode_mm_instr k (l ++ r)       /F/ encode_state (k + length l,v) → encode_state (k',v').
Proof with eauto; try omega.
  revert k. induction l; cbn - [subcode] in *; intros.
  - revert H0. ring_simplify (k + 0). eauto.
  - revert H0. ring_simplify (k + S (length l)). intros H1. destruct a.
    + econstructor 2. intros [[|] % divides_mult_inv | ] % divides_mult_inv; eauto.
      * eapply primestream_divides in H0; omega.
      * now eapply ps_qs_div in H0. 
      * eapply divides_encode_state in H0; omega.
      * specialize IHl with (k := S k). revert IHl.
        cbn - [subcode]. ring_simplify (S (k + length l)).
        intros IHl. eapply IHl. 2:exact H1.
        intros ? ? ?. eapply H. eapply subcode_cons. eassumption.
    + repeat econstructor 2. 2:unfold encode_dec2.
      2,3: cbn- [subcode]. 1: intros [] % divides_mult_inv_l.
      2: intros [ | ] % divides_mult_inv...
      * eapply divides_mult_inv in H0 as [? | ?]...
        eapply primestream_divides in H0...
        eapply divides_encode_state in H0... 
      * eapply primestream_divides in H0... subst.
        eapply (H n p). eauto.
      * eapply divides_encode_state in H0...
      * specialize (IHl (S k)). revert IHl.
        cbn - [subcode]. ring_simplify (S (k + length l)).
        intros IHl. eapply IHl. 2:exact H1.
        intros ? ? ?. eapply H. eapply subcode_cons. eassumption.
Qed.

Lemma qs_exp i n u (v : vec nat n) :
  divides (qs u) (encode_state (i,v)) <-> divides (qs u) (exp 0 v).
Proof.
  split.
  - intros [ | ] % divides_mult_inv; eauto.
    now eapply qs_ps_div in H.
  - intros. unfold encode_state. now eapply divides_mult.
Qed.

Lemma qs_encode_state i n (u : pos n) (v : vec nat n) :
  divides (qs u) (encode_state (i,v)) <-> v #> u > 0.
Proof.
  rewrite qs_exp.
  enough (forall i, divides (qs (i + u)) (exp i v) <-> v #> u > 0). eapply H. intros j.
  induction v.
  - inversion u.
  - revert u. eapply pos.pos_S_invert.
    + cbn; rewrite pos2nat_fst, Nat.add_0_r. 
      split.
      * intros [ | ] % divides_mult_inv; eauto.
        -- destruct x; try omega. cbn in H. 
           apply divides_1_inv in H.
           generalize (str_prime qs j); rewrite H.
           intros [ [] _ ]; auto.
        -- eapply qs_exp_div in H; now eauto.
      * intros. destruct x. inv H.
        exists (qs j ^ x * exp (S j) v). cbn. ring.
    + cbn. intros. rewrite <- IHv, pos2nat_nxt.
      rewrite qs_shift with (m := 1).
      simpl.
      replace (j+S (pos2nat p)) with (S (j+p)); try tauto.
      2: rewrite (plus_comm _ (S _)); simpl; rewrite plus_comm; auto.
      split; intros H.
      * eapply divides_mult_inv in H as [ | ]; eauto.
        eapply divides_pow in H; auto. 
        eapply primestream_divides in H.
        omega.
      * eapply divides_mult. 
        revert H; cbn; rewrite plus_n_Sm; eauto.
Qed.

Lemma one_step_forward m i P i1 v1 i2 v2 :
     @mm_no_self_loops m (i,P) 
  -> (i, P)              /MM/ (i1, v1)           → (i2,v2) 
  -> encode_mm_instr i P /F/  encode_state (i1,v1) → encode_state (i2,v2).
Proof with eauto; try omega.
  intros HP (k & l & [ u | u j ] & r & v & ? & ? & ?); inversion H; subst; clear H.
  - inversion H0; inversion H1; subst; clear H0 H1. 
    eapply skip_steps...
    econstructor. cbn. ring_simplify.
    replace (1 + (k + length l)) with (k + length l + 1) by omega. unfold encode_state, fst, snd. 
    rewrite vec_prod_mult.
    rewrite Nat.add_0_r; ring.
  - inversion H0; inversion H1; subst; clear H0 H1.
    all:eapply skip_steps...
    + cbn. econstructor 2.
      intros [] % divides_mult_inv_l...
      eapply divides_mult_inv in H0 as [ | ]...
      * now eapply qs_ps_div in H0.          
      * eapply qs_encode_state in H0. omega.
      * unfold encode_dec2. econstructor. unfold encode_state, fst, snd. ring.
    + econstructor. cbn. unfold encode_state, fst, snd. ring_simplify.
      replace (1 + (k + length l)) with (k + length l + 1) by omega.
      erewrite <- (vec_prod_div _ _ _ H4).
      rewrite Nat.add_0_r; ring.
Qed.

Lemma steps_forward m i P i1 v1 i2 v2 k :
    @mm_no_self_loops m (i, P) 
 -> (i, P) /MM/ (i1, v1) -[k]-> (i2,v2)
 -> encode_mm_instr i P /F/ encode_state (i1,v1) -[k]-> encode_state (i2,v2).
Proof.
  intros HP H. revert v1 i1 i2 H. induction k; intros v1 i1 i2 H; inversion H; subst; clear H; cbn.
  - reflexivity.
  - destruct st2. eapply one_step_forward in H1; eauto.
Qed.

Lemma one_step_backward m i P i1 v1 st :
     @mm_no_self_loops m (i, P)
  -> encode_mm_instr i P /F/ @encode_state m (i1,v1) → st 
  -> exists i2 v2, st = @encode_state m (i2,v2)
                /\ (i, P) /MM/ (i1, v1) → (i2,v2).
Proof.
  intros H1 H2.
  Check fractran_step_inv.
  destruct fractran_step_inv with (1 := H2)
    as (l & p & q & r & H3 & H4 & H5).
  Check encode_mm_instr_in_inv.
  destruct encode_mm_instr_in_inv
   
  
  intros H1 H2.
   destruct step_inv with (2 := H2)
        as (i2 & v2 & ->); auto.
   apply one_step_backward in H2; eauto.
Qed.


Ltac list_without L v :=
  match L with
  | ?L * v => list_without L v
  | v * ?L => list_without L v
  | ?L * ?R => let l := list_without L v in
              let r := list_without R v in constr:(l * r)
  | ?L => constr:(L)
  end.

Ltac factorout H v :=
  match type of H with ?L = ?R =>
                       let L := list_without L v in
                       let R := list_without R v in
                       let H' := fresh "H" in
                       rename H into H';
                       assert (H : L = R); [ eapply Nat.mul_cancel_l with v; [ eauto | ring_simplify; ring_simplify in H'; (rewrite H' || rewrite <- H'); ring] | ]; clear H'
  end.

Lemma mm_no_self_loops_cons n i a P : mm_no_self_loops   (i, a :: P) 
                                  -> @mm_no_self_loops n (1 + i, P).
Proof.
  intros ? ? ? ?. 
  eapply (H i0 x). 
  now eapply subcode_cons.
Qed. 

Hint Resolve mm_no_self_loops_cons.

Lemma one_step_backward m i P i1 v1 i2 v2 :
     @mm_no_self_loops m (i, P) 
  -> encode_mm_instr i P /F/  encode_state (i1,v1) → encode_state (i2,v2)
  ->              (i, P) /MM/ (i1, v1)           → (i2,v2).
Proof with eauto; try omega.
  revert i i1 i2 v1 v2.  induction P; intros i i1 i2 v1 v2 HP H; cbn; inv H.
  all: destruct a; inv H0. all:unfold encode_state, fst, snd in *. all: try ring_simplify in H1.
  all: try ring_simplify in H2.
  - assert (i = i1) as ->. {
      match type of H1 with _ = ?r => assert (divides (ps i) r) end.
      rewrite <- H1. exists (ps i2 * exp 0 v2). ring.
      eapply divides_mult_inv in H as [[[ | ] % divides_mult_inv | ] % divides_mult_inv | ]...
      + eapply primestream_divides in H. omega.
      + now eapply ps_qs_div in H.
      + eauto using primestream_divides.
      + now eapply ps_exp in H.
    } ring_simplify  in H1.
    factorout H1 (ps i1).
    
    assert (i2 = i1 + 1) as ->. {
      assert (divides (ps i2) (ps (i1 + 1) * qs p0 * exp 0 v1)).
      rewrite <- H1. exists (exp 0 v2). ring.
      eapply divides_mult_inv in H as [[ | ] % divides_mult_inv | ]...
      + eapply primestream_divides in H; eauto.
      + now eapply ps_qs_div in H.
      + now eapply ps_exp in H.
    } clear IHP.

    factorout H1 (ps (i1 + 1)).
    rewrite <- exp_inv_inc in H1. eapply exp_inj in H1 as ->.
    
    exists i1,[],(INC p0), P, v1. repeat split; try f_equal.
    cbn. omega. replace (i1 + 1) with (1 + i1) by omega. econstructor.
  - assert (i = i1) as ->.
    { match type of H1 with _ = ?r => assert (divides (ps i) r) end.
      rewrite <- H1. exists (qs p0 * ps i2 * exp 0 v2). ring.
      eapply divides_mult_inv in H as [[ | ] % divides_mult_inv | ]...
      + eapply primestream_divides in H...
      + eapply primestream_divides in H...
      + eapply ps_exp in H...
    } factorout H1 (ps i1).

    assert (i2 = i1 + 1) as ->. {
      match type of H1 with _ = ?r => assert (divides (ps i2) r) end.
      rewrite <- H1. exists (qs p0 * exp 0 v2). ring.
      eapply divides_mult_inv in H as [ | ]... 
      + eapply primestream_divides in H...
      + eapply ps_exp in H...
    } clear IHP. factorout H1 (ps (i1 + 1)).
    symmetry in H1. rewrite <- exp_inv_inc in H1. eapply exp_inj in H1 as ->.

    eexists i1,[], (DEC p0 n), P, _. repeat split; try f_equal.
    cbn. omega. replace (i1 + 1) with (1 + i1) by omega.
    pose proof (@in_mm_sss_dec_1 _ i1 p0 n (vec_change v2 p0 (S (vec_pos v2 p0))) (vec_pos v2 p0)).
    rewrite vec_change_eq in H... specialize (H eq_refl).
    now rewrite vec_change_idem, vec_change_same in H.
  - eapply IHP in H2. all: try now (cbn in *; omega).
    destruct H2 as (k & l & [ u | u j ] & r & v & ? & ? & ?).
    + inv H. inv H0. inv H2. 
      exists i. exists (INC p0 :: l). exists (INC u). exists r. exists v.
      cbn. repeat split. f_equal. omega.
      econstructor.
    + inv H. inv H0. inv H2. 
      * exists i. exists (INC p0 :: l). exists (DEC u i2). exists r. exists v2.
        cbn. repeat split. f_equal. omega.
        econstructor. eauto.
      * exists i. exists (INC p0 :: l). exists (DEC u j). exists r. exists v.
        cbn. repeat split. f_equal. omega.
        econstructor. eauto.
    + eauto.
  -  unfold encode_dec2 in H2. cbn in H2. inv H2.
     * assert (i = i1) as ->.
       { match type of H6 with _ = ?r => assert (divides (ps i) r) end.
         rewrite <- H6. exists (ps i2 * exp 0 v2). ring. ring_simplify in H.
         eapply divides_mult_inv in H as [[|] % divides_mult_inv | ]...
         + eapply primestream_divides in H... subst.
           edestruct (HP n p0)...
         + eapply primestream_divides in H...
         + eapply ps_exp in H...
       } factorout H6 (ps i1).

       assert (i2 = n) as ->. {
         match type of H6 with _ = ?r => assert (divides (ps i2) r) end.
         rewrite <- H6. exists (exp 0 v2). ring.
         eapply divides_mult_inv in H as [ | ]...
         + eapply primestream_divides in H... 
         + eapply ps_exp in H...
       } clear IHP.
       rewrite Nat.mul_cancel_l in H6...

       eapply exp_inj in H6 as ->.

       eexists i1,[], (DEC p0 n), P, _. repeat split; try f_equal.
       cbn. omega. eapply in_mm_sss_dec_0.

       destruct (gt_0_eq (vec_pos v1 p0)); try omega.
       eapply qs_encode_state with (i := i1 + 1) in H. destruct H1.
       destruct H.
       exists x. ring_simplify. repeat rewrite <- mult_assoc. rewrite <- H.
       unfold encode_state, fst, snd. ring.
     * eapply IHP in H7. subst.
       destruct H7 as (k & l & [ u | u j ] & r & v & ? & ? & ?).
       -- inv H. inv H0. inv H2.
          exists i. exists (DEC p0 n :: l). exists (INC u). exists r. exists v.
          cbn. repeat split. f_equal. omega.
          econstructor.
       -- inv H. inv H0. inv H2.
          ++ exists i. exists (DEC p0 n :: l). exists (DEC u i2). exists r. exists v2.
             cbn. repeat split. f_equal. omega.
             econstructor. eauto.
          ++ exists i. exists (DEC p0 n :: l). exists (DEC u j). exists r. exists v.
             cbn. repeat split. f_equal. omega.
             econstructor. eauto.
       -- eauto.
Qed.

Lemma step_inv m i P i1 (v1 : vec nat m) st :
     @mm_no_self_loops m (i,P) 
  -> encode_mm_instr i P /F/ encode_state (i1,v1) → st 
  -> exists i2 v2, st = @encode_state m (i2,v2).
Proof with eauto; try omega.
  intros HP ?. revert i H HP. induction P; intros i H0 HP.
  - cbn in H0. inv H0.
  - cbn in H0. inv H0.
    + destruct a; inv H.
      * exists (i + 1), (vec_change v1 p0 (S (v1 #> p0))).
        unfold encode_state in H1.
        assert (i = i1) as ->. {
          match type of H1 with _ = ?r => assert (divides (ps i) r) end.
          rewrite <- H1. exists st. ring.
          eapply divides_mult_inv in H as [ [|] % divides_mult_inv | [|] % divides_mult_inv ]...
          + eapply primestream_divides in H...
          + eapply ps_qs_div in H...
          + eapply primestream_divides in H...
          + eapply ps_exp in H...
        } unfold fst, snd in *; ring_simplify  in H1.
        factorout H1 (ps i1). subst.
        unfold encode_state, fst, snd. rewrite vec_prod_mult. replace (p0 + 0) with (0 + p0) by omega.
        cbn. ring.
      * unfold encode_state, fst, snd in H1.
        assert (i = i1) as ->. {
          match type of H1 with _ = ?r => assert (divides (ps i) r) end.
          rewrite <- H1. exists (qs p0 * st). ring.
          eapply divides_mult_inv in H as [ | [|] % divides_mult_inv ]...
          + eapply primestream_divides in H...
          + eapply primestream_divides in H...
          + eapply ps_exp in H...
        } 
        factorout H1 (ps i1).

        assert (v1 #> p0 > 0). {
          eapply qs_encode_state.
          match type of H1 with _ = ?r => assert (divides (qs p0) r) end.
          rewrite <- H1. exists st. ring. eapply H.
        }
        destruct (v1 #> p0) eqn:E. inv H.
        
        exists (i1+1), (vec_change v1 p0 n0).
        eapply Nat.mul_cancel_l. 2:rewrite H1. eauto.
        unfold encode_state, fst, snd. ring_simplify.
        rewrite <- !mult_assoc. rewrite Nat.mul_cancel_l. 2:eauto.
        rewrite <- (vec_prod_div _ _ _ E). replace (p0 + 0) with (0 + p0) by omega.
        cbn. ring.
    + destruct a; inv H.
      * eapply IHP in H2...
      * inv H2.
        -- unfold encode_state, fst, snd in H6.
           assert (i = i1) as ->. {
             match type of H6 with _ = ?r => assert (divides (ps i) r) end.
             rewrite <- H6. exists st. ring.
             eapply divides_mult_inv in H as [  | [|] % divides_mult_inv ]...
             + eapply primestream_divides in H. subst. destruct (HP n p0)...
             + eapply primestream_divides in H...
             + eapply ps_exp in H...
           } 
           factorout H6 (ps i1). subst.
           unfold encode_state, fst, snd. eexists; eauto.
        -- eapply IHP in H7...
Qed.

Lemma step_backward m i P i1 v1 st :
     @mm_no_self_loops m (i, P)
  -> encode_mm_instr i P /F/ @encode_state m (i1,v1) → st 
  -> exists i2 v2, st = @encode_state m (i2,v2)
                /\ (i, P) /MM/ (i1, v1) → (i2,v2).
Proof.
  intros H1 H2.
   destruct step_inv with (2 := H2)
        as (i2 & v2 & ->); auto.
   apply one_step_backward in H2; eauto.
Qed.

Lemma steps_backward m i P i1 v1 k st :
     @mm_no_self_loops m (i, P)
  ->               encode_mm_instr i P /F/ encode_state (i1,v1) -[k]-> st 
  -> exists i2 v2, (i, P) /MM/ (i1, v1) -[k]-> (i2,v2)
                /\ st = encode_state (i2,v2). 
Proof.
  intros H1.
  revert i1 v1 st; induction k as [ | k IHk ]; intros i1 v1 st H; simpl in H.
  - subst; exists i1, v1; split; auto; constructor.
  - destruct H as (st1 & H2 & H3).
    destruct step_backward with (2 := H2)
      as (i2 & v2 & -> & H5); auto.
    destruct IHk with (1 := H3) as (i3 & v3 & ? & ->).
    exists i3, v3; split; auto.
    constructor 2 with (i2,v2); auto.
Qed.

(** DLW: I did rewrite that proof to be sure I did not miss
    an argument for the paper *)

Theorem mm_fractran_simulation n P v :
     @mm_no_self_loops n (1, P) 
  -> (1,P) /MM/ (1,v) ↓ <-> encode_mm_instr 1 P /F/ ps 1 * exp 0 v ↓.
Proof.
  intros HP.
  change (ps 1* exp 0 v) with (encode_state (1,v)).
  split.
  + intros ((j,w) & (k & H1) & H2); simpl fst in *.
    exists (encode_state (j,w)); split.
    * exists k; apply steps_forward in H1; auto.
    * intros x Hx.
      destruct step_backward with (2 := Hx)
        as (i2 & v2 & -> & ?); auto.
      revert H; apply sss_out_step_stall; auto.
  + intros (st & (k & H1) & H2).
    destruct steps_backward with (2 := H1)
      as (i2 & v2 & H3 & ->); auto.
    exists (i2,v2); split.
    * exists k; auto.
    * simpl fst.
      destruct (in_out_code_dec i2 (1,P)) as [ H4 | H4 ]; auto; exfalso.
      destruct in_code_subcode with (1 := H4) as (rho & l & r & G1 & G2).
      destruct (mm_sss_total rho (i2,v2)) as ((i3,v3) & G3).
      apply H2 with (encode_state (i3,v3)).
      apply one_step_forward; auto.
      subst P; apply in_sss_step; auto.
Qed.

Theorem mm_fractran_n n (P : list (mm_instr n)) : 
        { l |  Forall (fun c => snd c <> 0) l
            /\ forall v, (1,P) /MM/ (1,v) ↓ <-> l /F/ ps 1 * exp 1 v ↓ }.
Proof.
   destruct mm_remove_self_loops with (P := P) as (Q & H1 & _ & H2).
   exists (encode_mm_instr 1 Q); split. 
   + generalize (encode_mm_instr_regular 1 Q); apply Forall_impl; intros; tauto.
   + intros x.
     rewrite H2, mm_fractran_simulation; auto.
     simpl exp; rewrite Nat.add_0_r; tauto.
Qed.

Theorem mm_fractran n (P : list (mm_instr (S n))) : 
     { l | forall x, (1,P) /MM/ (1,x##vec_zero) ↓ <-> l /F/ ps 1 * qs 1^x ↓ }.
Proof.
   destruct mm_fractran_n with (P := P) as (l & _ & Hl).
   exists l; intros x; rewrite Hl; simpl.
   rewrite exp_zero, Nat.mul_1_r; tauto.
Qed.
