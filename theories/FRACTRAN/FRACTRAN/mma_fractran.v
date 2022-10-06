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

(* ** Compiler from MM to FRACTRAN *)

Require Import List Arith Lia Permutation.

Import ListNotations.

From Undecidability.Shared.Libs.DLW 
  Require Import utils utils_tac utils_list utils_nat gcd rel_iter prime
                 pos vec subcode sss.

From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_no_self.
From Undecidability.FRACTRAN Require Import FRACTRAN fractran_utils prime_seq FRACTRAN_sss.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db. 

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I // s -1> t" := (mma_sss I s t).
Local Notation "P /MMA/ s → t" := (sss_step (@mma_sss _) P s t) (at level 70, no associativity). 
Local Notation "P /MMA/ s -[ k ]-> t" := (sss_steps (@mma_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /MMA/ s ▹ t" := (sss_output (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MMA/ s ↓" := (sss_terminates (@mma_sss _) P s) (at level 70, no associativity).

Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).
Local Notation "l /F/ x -[ k ]-> y" := (fractran_steps l k x y) (at level 70, no associativity).
Local Notation "l /F/ x ▹ y" := (fractran_eval l x y) (at level 70, no associativity).

Set Implicit Arguments.

(* Fractran simulates MMA *)

(*       let a MMA program 1: INC ... k: DEC ... n: _ *)
(*       with variables x1...xm *)

(*    we use p1...pn,q1...qm distinct primes and  *)
(*    encode the state (i,v1,...,vm) *)
(*    as p1^0*...*pi^1*...*pn^0*q1^v1*...*qm^vm *)

(*    i: INC xu   ---> (qu*p(i+1) / pi) *)
(*    i: DEC xu j ---> (pj / pi*qu) and (p(i+1) / pi) (the second constraint should appear AFTER in the list) *)

Local Definition encode_inc  n i (u : pos n) := (ps (i + 1) * qs u, ps i).
Local Definition encode_dec  n i (u : pos n) j := (ps j, ps i * qs u).
Local Definition encode_dec2 n i (u : pos n) (_ : nat) := (ps (i + 1), ps i).

Local Definition encode_one_instr m i (rho : mm_instr (pos m)) :=
  match rho with
    | INC u   => encode_inc i u :: nil
    | DEC u j => encode_dec i u j :: encode_dec2 i u j :: nil
  end.

Local Fixpoint encode_mma_instr n i (l : list (mm_instr (pos n))) : list (nat * nat) :=
  match l with
    | nil      => nil
    | rho :: l => encode_one_instr i rho ++ encode_mma_instr (S i) l
  end.

Local Fact encode_mma_instr_app n i l r : @encode_mma_instr n i (l++r) = encode_mma_instr i l 
                                                                      ++ encode_mma_instr (length l+i) r.
Proof.
  revert i; induction l as [ | ? ? IHl ]; intros ?; simpl; auto; rewrite IHl, app_ass.
  do 3 f_equal; lia.
Qed.

Local Fact encode_mma_instr_regular n i l : Forall (fun c => fst c <> 0 /\ snd c <> 0) (@encode_mma_instr n i l).
Proof.
  revert i; induction l as [ | [ | ] ]; intro; simpl.
  + constructor.
  + constructor; auto; unfold encode_inc; simpl; split;
      [ apply Nat.neq_mul_0; split | ]; apply prime_neq_0; apply nthprime_prime.
  + constructor; [ | constructor ]; auto; split; unfold encode_dec, encode_dec2; simpl.
    2: apply Nat.neq_mul_0; split.
    all: apply prime_neq_0; apply nthprime_prime.
Qed.

Local Fact encode_mma_instr_regular' n i l : fractran_regular (@encode_mma_instr n i l).
Proof. generalize (encode_mma_instr_regular i l); apply Forall_impl; tauto. Qed.

Local Fact encode_mma_instr_in_inv n i P el c er :
          @encode_mma_instr n i P = el++c::er
       -> exists l rho r, P = l++rho::r /\ In c (encode_one_instr (length l+i) rho).
Proof.
  revert i el c er; induction P as [ | rho P IHP ]; simpl; intros i el c er H.
  + now destruct el.
  + destruct list_app_cons_eq_inv with (1 := H)
      as [ (m & H1 & H2) | (m & H1 & H2) ].
    * destruct IHP with (1 := H2) as (l & rho' & r & G1 & G2).
      exists (rho::l), rho', r; subst; split; auto.
      eq goal G2; do 2 f_equal; simpl; lia.
    * exists nil, rho, P; split; simpl; auto.
      rewrite <- H1; apply in_or_app; simpl; auto.
Qed.

Local Notation divides_mult_inv := prime_div_mult.

Local Ltac inv H := inversion H; subst; clear H.

(* ps n = nthprime (2n); sq = nthprim (2n+1) *)

Local Lemma ps_prime n : prime (ps n).
Proof. apply nthprime_prime. Qed.

#[local] Opaque ps qs.

(* The divisibility results are no so complicated when
    we do not need to show that encode_state is injective ... *)

Local Fact divides_from_eq x y t : x*y = t -> divides x t.
Proof. intros <-; apply divides_mult_r, divides_refl. Qed.

Local Fact prime_div_mult3 p x y z : prime p -> divides p (x*y*z) -> divides p x \/ divides p y \/ divides p z.
Proof. intros ? [ [] % prime_div_mult | ] % prime_div_mult; auto. Qed.

Local Fact prime_div_mult4 p w x y z : prime p -> divides p (w*x*y*z) -> divides p w \/ divides p x \/ divides p y \/ divides p z.
Proof. intros ? [ [] % prime_div_mult | ] % prime_div_mult3; auto. Qed.

(** Gödel encoding if MMA states as numbers *)

Local Definition encode_state {n} (c : nat * vec nat n) := ps (fst c) * exp 0 (snd c).

Local Lemma divides_ps_encode_state i k n (v : vec nat n) :
  divides (ps i) (encode_state (k,v)) <-> i = k.
Proof.
  unfold encode_state; split. 
  * induction v as [ | n x v IHv ].
    - simpl; replace (ps k * 1) with (ps k) by lia.
      apply primestream_divides.
    - simpl; intros [ H | [ H | H ] % divides_mult_inv ] % divides_mult_inv; eauto.
      + now eapply primestream_divides in H.
      + now apply divides_pow, ps_qs_div in H; auto.
      + now eapply ps_exp in H.
  * intros <-; simpl; apply divides_mult_r, divides_refl.
Qed.

Local Lemma divides_qs_encode_state i k n (v : vec nat n) :
  divides (qs i) (encode_state (k,v)) <-> divides (qs i) (exp 0 v).
Proof.
  split.
  - intros [ | ] % divides_mult_inv; eauto.
    now eapply qs_ps_div in H.
  - intros. 
    unfold encode_state.
    now eapply divides_mult.
Qed.

Local Lemma qs_encode_state i n (u : pos n) (v : vec nat n) :
  divides (qs u) (encode_state (i,v)) <-> v#>u > 0.
Proof.
  rewrite divides_qs_encode_state.
  enough (forall i, divides (qs (i + u)) (exp i v) <-> v #> u > 0). 
  1: eapply H.
  intros j; revert u; induction v as [ | x n v IHv ]; intros u; invert pos u.
  - cbn; rewrite pos2nat_fst, Nat.add_0_r. 
    split.
    * intros [ H | H ] % divides_mult_inv; eauto.
      + destruct x; try lia; cbn in H. 
        apply divides_1_inv in H.
         generalize (str_prime qs j); rewrite H.
         intros [] % not_prime_1.
      + now apply qs_exp_div in H; auto.
    * intros H; destruct x as [|x]; try lia; clear H.
      simpl; apply divides_mult_r, divides_mult_r, divides_refl.
  - rewrite <- IHv, pos2nat_nxt.
    rewrite qs_shift with (m := 1).
    simpl.
    replace (j+S (pos2nat u)) with (S (j+u)).
    2: now rewrite (plus_comm _ (S _)); simpl; rewrite plus_comm.
    split; intros H.
    * apply divides_mult_inv in H as [ | ]; auto. eauto.
       apply divides_pow in H; auto. 
       apply primestream_divides in H; lia.
    * now apply divides_mult.
Qed.

Local Lemma encode_state_inj n st1 st2 :
  @encode_state n st1 = @encode_state n st2 -> st1 = st2.
Proof.
  intros H.
  destruct st1 as (i1, v1), st2 as (i2, v2).
  assert (i1 = i2); subst.
  - eapply divides_ps_encode_state. rewrite <- H. 
    unfold encode_state. cbn. rewrite mult_comm. eapply divides_mult, divides_refl.
  - f_equal. unfold encode_state in H. cbn in H.
    replace (ps i2) with (ps i2 ^ 1) in H by (cbn; lia).
    eapply power_factor_uniq in H as [_ H].
    + eapply exp_inj. eauto.
    + pose proof (ps_prime i2) as ? % prime_ge_2. lia.
    + eapply ps_exp.
    + eapply ps_exp.
Qed.

(** Skiping over leading fractions *)

Local Lemma skip_steps n k l r (v : vec _ n) st :
      @mma_no_self_loops n (k, l ++ r) 
   -> encode_mma_instr (k + length l) r  /F/ encode_state (k + length l,v) → encode_state st
   -> encode_mma_instr  k       (l ++ r) /F/ encode_state (k + length l,v) → @encode_state n st.
Proof with eauto; try lia.
  revert k.
  induction l as [ | rho l IHl ]; cbn - [subcode] in *; intros k.
  - ring_simplify (k + 0); auto.
  - ring_simplify (k + S (length l)).
    intros Hk H. 
    destruct rho as [ u | u j ].
    + constructor 2. 
      * intros [[ H1 | H1 ] % divides_mult_inv | H1 ] % divides_mult_inv; eauto.
        -- apply primestream_divides in H1; lia.
        -- now apply ps_qs_div in H1. 
        -- apply divides_ps_encode_state in H1; lia.
      * specialize IHl with (k := 1+k). 
        revert IHl; cbn - [subcode]; ring_simplify (S (k + length l)); intros IHl.
        apply IHl; trivial.
        revert Hk; apply mma_no_self_loops_cons_inv.
    + repeat constructor 2.
      * intros [[H1|H1] % divides_mult_inv [H2|H2] % divides_mult_inv ] % divides_mult_inv_l...
        -- now apply qs_ps_div in H2.
        -- apply primestream_divides in H1; subst.
           eapply (Hk j u); auto.
        -- now apply qs_ps_div in H2.
        -- apply divides_ps_encode_state in H1...
      * intros [H1|H1] % divides_mult_inv...
        -- apply primestream_divides in H1...
        -- apply divides_ps_encode_state in H1...
      * specialize (IHl (S k)). 
        revert IHl; cbn - [subcode]; ring_simplify (S (k + length l)); intros IHl.
        apply IHl; trivial.
        revert Hk; apply mma_no_self_loops_cons_inv.
Qed.

Local Hint Resolve encode_mma_instr_regular' : core.

Section steps_forward.

  Variable (n i : _) (P : list (mm_instr (pos _)))
           (HP : @mma_no_self_loops n (i,P)).

  Local Lemma one_step_forward st1 st2 :
                       (i,P) /MMA/             st1 →              st2 
    -> encode_mma_instr i P  /F/  encode_state st1 → encode_state st2.
  Proof using HP.
    intros (k & l & rho & r & v & H1 & H2 & H3).
    inversion H1; subst i P; clear H1.
    destruct H3 as [ i x v1 | i x j v1 | i x j v1 u ]; 
      inversion H2; subst i v1; clear H2;
      apply skip_steps; auto.
    + constructor.
      ring_simplify.
      replace (1 + (k + length l)) with (k + length l + 1) by lia. 
      unfold encode_state, fst, snd.
      rewrite vec_prod_mult.
      rewrite Nat.add_0_r; ring.
    + simpl; constructor 2.
      * intros [H2 H3] % divides_mult_inv_l...
        eapply divides_mult_inv in H3 as [ H3 | H3 ]; auto...
        -- now apply qs_ps_div in H3.
        -- apply qs_encode_state in H3; lia.
      * constructor.
        unfold encode_state, fst, snd.
        replace (k + length l + 1) with (S (k + length l)); ring.
    + simpl; constructor.
      unfold encode_state, fst, snd.
      rewrite <- vec_prod_div with (1 := H), Nat.add_0_r; ring.
  Qed.

  Local Lemma steps_forward k st1 st2 :
                       (i,P) /MMA/            st1 -[k]->              st2
    -> encode_mma_instr i P  /F/ encode_state st1 -[k]-> encode_state st2.
  Proof using HP.
    induction 1 as [ st1 | k st1 st2 st3 H1 H2 IH2 ].
    + simpl; reflexivity.
    + exists (encode_state st2); split; auto.
      now apply one_step_forward.
  Qed.

End steps_forward.

Section steps_backward.
  
  Variable (n i : _) (P : list (mm_instr (pos _)))
           (HP : @mma_no_self_loops n (i,P)).

  (* Since /F/ is functional and /MMA/ is total, we can use forward
     steps to recover backward steps *)

  Local Lemma one_step_backward i1 v1 st :
       encode_mma_instr i P /F/ encode_state (i1,v1) → st
    -> exists i2 v2, st = encode_state (i2,v2)
                  /\ (i,P) /MMA/ (i1,v1) → (i2,v2).
  Proof using HP.
    intros H2.
    destruct fractran_step_inv with (1 := H2)
      as (el & p & q & er & H3 & H4 & H5).
    apply divides_from_eq in H5.
    (* we search the instruction which generates p/q *)
    destruct encode_mma_instr_in_inv with (1 := H3)
      as (l & rho & r & -> & G2).
    (* the initial PC must be at instruction rho *)
    assert (length l + i = i1) as E.
    { apply divides_ps_encode_state with (v := v1).
      unfold encode_one_instr in G2.
      destruct rho as [ u | u j ]; unfold encode_inc, encode_dec, encode_dec2 in G2;
        [ destruct G2 as [ G2 | [] ] | destruct G2 as [ G2 | [ G2 | [] ] ] ]; 
        inversion G2; subst p q; clear G2;
        repeat rewrite mult_assoc in H5.
      * apply prime_div_mult3 in H5 as [ H5 | [ H5 | H5 ] ]; auto.
        + apply primestream_divides in H5; lia.
        + now apply ps_qs_div in H5.
      * apply divides_mult_inv_l in H5 as [ H5 _ ].
        apply prime_div_mult in H5 as [ H5 | H5 ]; auto.
        apply primestream_divides in H5; subst j.
        destruct HP with (length l+i) u; auto.
      * apply prime_div_mult in H5 as [ H5 | H5 ]; auto.
        apply primestream_divides in H5; lia. }
    destruct mma_sss_total with (ii := rho) (s := (i1,v1))
      as ((i2 & v2) & H7).
    exists i2, v2.
    assert ((i, l++rho::r) /MMA/ (i1,v1) → (i2,v2)) as H8.
    { apply in_sss_step; auto; simpl; lia. }
    split; auto.
    apply one_step_forward in H8; auto.
    revert H2 H8; apply fractran_step_fun; auto.
  Qed.

  Local Lemma steps_backward k i1 v1 st :
       encode_mma_instr i P /F/ encode_state (i1,v1) -[k]-> st
    -> exists i2 v2, (i, P) /MMA/ (i1, v1) -[k]-> (i2,v2)
                /\ st = encode_state (i2,v2). 
  Proof using HP.
    revert i1 v1 st; induction k as [ | k IHk ]; intros i1 v1 st H; simpl in H.
    - subst; exists i1, v1; split; auto; constructor.
    - destruct H as (st1 & H2 & H3).
      destruct one_step_backward with (1 := H2)
        as (i2 & v2 & -> & H5); auto.
      destruct IHk with (1 := H3) as (i3 & v3 & ? & ->).
      exists i3, v3; split; auto.
      constructor 2 with (i2,v2); auto.
  Qed.

End steps_backward.

Theorem mma_fractran_simulation n P v :
     @mma_no_self_loops n (1,P) 
  ->   (1,P) /MMA/ (1,v) ↓ 
   <-> encode_mma_instr 1 P /F/ ps 1 * exp 0 v ↓.
Proof.
  intros HP.
  change (ps 1* exp 0 v) with (encode_state (1,v)).
  split.
  + intros ((j,w) & (k & H1) & H2); simpl fst in *.
    exists (encode_state (j,w)); split.
    * exists k; apply steps_forward in H1; auto.
    * intros x Hx.
      destruct one_step_backward with (2 := Hx)
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
      destruct (mma_sss_total rho (i2,v2)) as ((i3,v3) & G3).
      apply H2 with (encode_state (i3,v3)).
      apply one_step_forward; auto.
      subst P; apply in_sss_step; auto.
Qed.

Theorem mma_fractran_simulation_forward n P v j v' :
     @mma_no_self_loops n (1,P) 
  -> (1,P) /MMA/ (1,v) ▹ (j,v') -> encode_mma_instr 1 P /F/ ps 1 * exp 0 v ▹ encode_state (j,v').
Proof.
  intros HP.
  change (ps 1* exp 0 v) with (encode_state (1,v)).
  intros ((k & H1) & H2); simpl fst in *.
  rewrite eval_iff. split.
  * exists k; apply steps_forward in H1; auto.
  * intros x Hx.
    destruct one_step_backward with (2 := Hx)
      as (i2 & v2 & -> & ?); auto.
    revert H; apply sss_out_step_stall; auto.
Qed.

Theorem mma_fractran_simulation_strong n P v j v' :
     @mma_no_self_loops n (1, P) 
  -> (1,P) /MMA/ (1,v) ▹ (j, v') <-> encode_mma_instr 1 P /F/ ps 1 * exp 0 v ▹ encode_state (j, v').
Proof.
  intros HP.
  change (ps 1* exp 0 v) with (encode_state (1,v)).
  split.
  - now eapply mma_fractran_simulation_forward.
  - intros [H1 H2] % eval_iff.
    edestruct mma_fractran_simulation as [_ [[j' w] Hw]]; [ eauto | eexists; eauto | ].
    pose proof (Hw' := Hw).
    eapply mma_fractran_simulation_forward in Hw as [Hw1 Hw2] % eval_iff; [ | eauto].
    eapply fractran_compute_fun in H1; eauto.
    enough ((j', w) = (j, v')) as <- by eassumption.
    eapply encode_state_inj in H1; eauto.
Qed.

Theorem mma_fractran_not_zero n (P : list (mm_instr (pos n))) : 
        { l |  Forall (fun c => fst c <> 0 /\ snd c <> 0) l
            /\ forall v, (1,P) /MMA/ (1,v) ↓ <-> l /F/ ps 1 * exp 0 v ↓ }.
Proof.
   destruct mma_remove_self_loops with (P := P) as (Q & H1 & _ & H2).
   exists (encode_mma_instr 1 Q); split. 
   + apply encode_mma_instr_regular.
   + intros x.
     rewrite H2, mma_fractran_simulation; tauto.
Qed.

Theorem mma_fractran_n n (P : list (mm_instr (pos n))) : 
        { l |  Forall (fun c => snd c <> 0) l
            /\ forall v, (1,P) /MMA/ (1,v) ↓ <-> l /F/ ps 1 * exp 0 v ↓ }.
Proof.
  destruct (mma_fractran_not_zero P) as (l & H1 & H2).
  exists l; split; auto.
  revert H1; apply Forall_impl; intros; tauto.
Qed.

Theorem mma_fractran n (P : list (mm_instr (pos (S n)))) : 
     { l | forall x, (1,P) /MMA/ (1,x##vec_zero) ↓ <-> l /F/ 5*3^x ↓ }.
Proof.
  destruct mma_fractran_n with (P := P) as (l & _ & Hl).
  rewrite <- ps_1, <- qs_0.
  exists l; intros x; rewrite Hl; simpl.
  rewrite exp_zero, Nat.mul_1_r; tauto.
Qed.
