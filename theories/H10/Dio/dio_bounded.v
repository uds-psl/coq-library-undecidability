(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** Object-level encoding of bounded universal quantification *)

From Stdlib Require Import Arith Lia List Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list sums bounded_quantification.

From Undecidability.H10.Matija 
  Require Import cipher.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_cipher dio_elem.

Set Implicit Arguments.

Local Abbreviation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).

(* We show the elimination of bounded universal quantification. The proof is
    based on the paper 

       "A new technique for obtaining Diophantine representations via 
        elimination of bounded universal quantifiers" by Matiyasevich (1997)

    with two noticable differences

    a) I use r = 2^(4*q) instead of r = 2^(2*q).

       2*q could work but I think the proof that cc = aa * bb is simulated 
       (implied by the paper -- the proof is not given) does not work well 
       because masked digits can be of the form f i * g j + f j * g i
       and f _ < 2^q,  g _ < 2^q implies f _ * g _ < 2^(2*q) which is
       good but *does not* imply  f _ * g _ + g _ * f _ < 2^(2*q) !!

       The argument could still work though it is going to be much
       more complicated to establish formally, so I raised 2*q to 4*q
       to solve straightforwardly the overflow problem of masked digits
       Anyway, this 2*q value was arbitrary so it only impacts the 
       proof in minor ways.

    b) The arguments outlined between (26) and (31) are flawed I think
       One should first split the k_i's in 

                 0 <= k_2 < .... < k_d <= 2^l+1 < .... < k_{m+1}

       to do the computation. The upper k_i's are masked out and then you 
       can show that d must be m+1 with the other constraints.
*)


Section dio_rel_bounded_fall.

  Section dio_bounded_elem.

    Variable (k : nat).

    (* ω : nat -> nat
       for i < k, ω represents the cipher of the corresponding variable x_i
       for i = k, ω represents the cipher of <0,...,l-1> 
       for i = k+1, ω contains the value q 
       for i = k+2, ω contains the value l   
       for k+2 < i, ω represents the value of parameter i-k-2>0  *)

    Abbreviation iq := (k+1).  (* The index of q in ω *)
    Abbreviation il := (k+2).  (* The index of l in ω *)

    Let dc_Code (c : dio_constraint) ω :=
      match c with
       | (u, dee_nat n)           => Const (ω il) (ω iq) n (ω u)
       | (u, dee_var v)           => ω u = ω v
       | (u, dee_par 0)           => ω u = ω k
       | (u, dee_par (S p))       => Const (ω il) (ω iq) (ω (k+2+p)) (ω u)
       | (u, dee_comp do_add v w) => Code_plus (ω u) (ω v) (ω w)  
       | (u, dee_comp do_mul v w) => Code_mult (ω il) (ω iq) (ω u) (ω v) (ω w)
      end.

    Local Fact dio_rel_dc_Code c : 𝔻R (dc_Code c).
    Proof. 
      destruct c as (u & [ n | v | [] | [] v w ]); unfold dc_Code; dio auto.
    Defined.

    Hint Resolve dio_rel_dc_Code : dio_rel_db.

   (*

      Eval compute in df_size_Z (proj1_sig (dio_rel_dc_Code (0,dee_comp do_mul 1 2))). 

    *)

    (* Case of do_mul gives the overall bound  

    Let dc_Code_size_Z c : (df_size_Z (proj1_sig (dio_rel_dc_Code c)) <= 203468)%Z.
    Proof.
      destruct c as (u & [ n | v | [] | [] v w ]); compute; discriminate.
    Qed. *)

    (*  ω         | (φ _)    ~  π    |  ν
        i < k     | i        |  i    | 
        i = k     | <0,..,l> |  ?    |
        i = k+1   |          |  q    |  
        i = k+2   |          |  l    |  0
        i > k+2   |          |       |  i-(k+2)  
     *)

    Local Fact dc_Code_spec c φ π ν ω : 
          (forall i, i < k -> is_cipher_of (ν 0) (π iq) (φ i) (π i))
       -> (is_cipher_of (ν 0) (π iq) (fun n => n) (π k))
       -> (forall x, dc_vars c x -> x < k)
       -> (forall i, i < il -> ω i = π i)
       -> (forall i, il <= i -> ω i = ν (i-il))
       -> dc_Code c ω 
      <-> forall j, j < ν 0 -> dc_eval (fun i => φ i j) (j·ν) c.
    Proof.
      intros G1 G2 G3 G4 G5.
      assert (ω il = ν 0) as G0.
      { rewrite G5; try lia; f_equal; lia. }
      destruct c as (u & [ n | v | [ | p ] | [] v w ]); simpl.
      + assert (u < k) as Hu. { apply G3; left; auto. }
        rewrite G0, G4, G4; try lia.
        specialize (G1 _ Hu).
        unfold dc_eval; simpl; split.
        * intros (g & Hg1 & Hg4).
          generalize (is_cipher_of_inj G1 Hg1); intros G6.
          intros; rewrite G6, Hg4; auto; lia.
        * intros; exists (φ u); split; auto.
      + assert (u < k) as Hu. { apply G3; cbv; auto. }
        assert (v < k) as Hv. { apply G3; cbv; auto. }
        do 2 (rewrite G4; try lia).
        unfold dc_eval; simpl.
        apply G1 in Hu.
        apply G1 in Hv.
        apply (is_cipher_of_equiv Hu Hv). 
      + assert (u < k) as Hu. { apply G3; cbv; auto. }
        do 2 (rewrite G4; try lia).
        unfold dc_eval; simpl.
        apply G1 in Hu.
        apply (is_cipher_of_equiv Hu G2).
      + rewrite G0, G4; try lia.
        rewrite G5; try lia.
        replace (il+p-il) with p by lia.
        assert (u < k) as Hu. { apply G3; cbv; auto. }
        rewrite G4; try lia.
        apply G1 in Hu.
        unfold dc_eval; simpl; split.
        * intros (g & Hg1 & Hg2).
          generalize (proj1 (is_cipher_of_equiv Hu Hg1) eq_refl); intros G6.
          intros; rewrite G6, Hg2; auto.
        * intro; exists (φ u); auto.
      + assert (Hu : u < k). { apply G3; cbv; auto. }
        assert (Hv : v < k). { apply G3; cbv; auto. }
        assert (Hw : w < k). { apply G3; cbv; auto. }
        do 3 (rewrite G4; try lia).
        apply G1 in Hu; apply G1 in Hv; apply G1 in Hw.
        rewrite Code_plus_spec with (1 := Hu) (2 := Hv) (3 := Hw).
        unfold dc_eval; simpl; tauto.
      + assert (Hu : u < k). { apply G3; cbv; auto. }
        assert (Hv : v < k). { apply G3; cbv; auto. }
        assert (Hw : w < k). { apply G3; cbv; auto. }
        rewrite G0; do 4 (rewrite G4; try lia).
        apply G1 in Hu; apply G1 in Hv; apply G1 in Hw.
        rewrite Code_mult_spec with (1 := Hu) (2 := Hv) (3 := Hw).
        unfold dc_eval; simpl; tauto.
    Qed.

    Local Definition dc_list_Code ll ν := fold_right (fun c P => dc_Code c ν /\ P) True ll.

    Local Fact dio_rel_dc_list_Code ll : 𝔻R (dc_list_Code ll).
    Proof. induction ll; unfold dc_list_Code; simpl; dio auto. Qed.

    Hint Resolve dio_rel_dc_list_Code : dio_rel_db.

    Local Fact dc_list_Code_spec ll φ π ν ω : 
          (forall i, i < k -> is_cipher_of (ν 0) (π iq) (φ i) (π i))
       -> (is_cipher_of (ν 0) (π iq) (fun n => n) (π k))
       -> (forall c, In c ll -> forall x, dc_vars c x -> x < k)
       -> (forall i, i < il  -> ω i = π i)
       -> (forall i, il <= i -> ω i = ν (i-il))
       -> dc_list_Code ll ω 
      <-> forall j, j < ν 0 -> Forall (dc_eval (fun i => φ i j) (j·ν)) ll.
    Proof.
      intros G1 G2 G3 G4 G5; revert G3.
      rewrite <- Forall_forall.
      induction 1 as [ | c ll F1 F2 IF2 ]; simpl.
      + split; auto.
      + rewrite IF2, dc_Code_spec; auto. 
        split.
        * intros (E1 & E2) j Hj; constructor; auto.
        * intros E1; split; intros j Hj; specialize (E1 _ Hj);
            rewrite Forall_cons_inv in E1; tauto.
    Qed.

    Local Definition ciphers ν := 
             CodeNat (ν il) (ν iq) (ν k) 
          /\ forall i, i < k -> Code (ν il) (ν iq) (ν i).

    Local Fact dio_rel_ciphers : 𝔻R ciphers.
    Proof.
      unfold ciphers; dio auto.
      apply dio_rel_finite_conj; intros; dio auto.
    Defined.

    Hint Resolve dio_rel_ciphers : dio_rel_db.

    Local Fact ciphers_spec ν : 
           ciphers ν <-> is_cipher_of (ν il) (ν iq) (fun n => n) (ν k) 
                      /\ exists φ, forall i, i < k -> is_cipher_of (ν il) (ν iq) (φ i) (ν i).
    Proof. 
      unfold ciphers, Code, CodeNat.
      split; intros (H1 & H2); split; auto; clear H1.
      + apply fmap_reifier_default in H2; auto.
      + destruct H2 as (phi & Hphi).
        intros i Hi; exists (phi i); auto.
    Qed.

    Variables (ll : list dio_constraint) 
              (Hll : forall c x, In c ll -> dc_vars c x -> x < k).

    Let Hll' : forall c, In c ll -> forall x, dc_vars c x -> x < k.
    Proof. intros c ? x ?; apply (@Hll c x); auto. Qed.

    Let pre_quant ν := ν il+1 < ν iq /\ ciphers ν /\ dc_list_Code ll ν.

    Let dio_rel_pre_quant : 𝔻R pre_quant.
    Proof. unfold pre_quant; dio auto. Defined.

    Let dc_list_bfall ν := exists π, pre_quant (fun i => if le_lt_dec il i then ν (i-il) else π i).

    Let dc_list_bfall_spec_1 ν :
            dc_list_bfall ν 
        <-> exists q φ, ν 0+1 < q 
                    /\ (forall i j, i < k -> j < ν 0 -> φ i j < power q 2) 
                    /\  forall j, j < ν 0 -> Forall (dc_eval (fun i => φ i j) (j·ν)) ll.
    Proof.
      split.
      + intros (pi & G0 & G1 & G4).
        rewrite ciphers_spec in G1.
        destruct (le_lt_dec il k) as [ ? | _ ]; try lia.
        destruct (le_lt_dec il il) as [ _  | ? ]; try lia.
        destruct (le_lt_dec il iq) as [ ? | _ ]; try lia.
        replace (il-il) with 0 in * by lia.
        destruct G1 as (G1 & phi & G3).
        assert (forall i, i < k -> is_cipher_of (ν 0) (pi iq) (phi i) (pi i)) as G2.
        { intros i Hi; generalize (G3 _ Hi); destruct (le_lt_dec il i); auto; lia. }
        clear G3.
        rewrite dc_list_Code_spec with (π := pi) (φ := phi) (ν := ν) in G4; auto.
        2,3: intros i Hi; destruct (le_lt_dec il i) as [ H | H ]; auto; try lia.
        exists (pi iq), phi; repeat (split; auto). 
        intros i j Hi Hj; destruct (G2 _ Hi) as (_ & G3 & _); auto.
      + intros (q & phi & Hq & Hphi1 & Hphi2).
        assert (q <= power q 2) as Hq' by (apply power_ge_n; auto).
        destruct (the_cipher (fun i => i) Hq) as (u & Hu). { intros; lia. }

        set (pi i := match lt_eq_lt_dec i k with
                     | inleft (left H)  => proj1_sig (the_cipher (phi i) Hq (fun j Hj => Hphi1 _ _ H Hj)) 
                     | inleft (right H) => u
                     | inright H        => q
                   end).
        assert (Hpi_k : pi k = u).
        { unfold pi; destruct (lt_eq_lt_dec k k) as [ [] | ]; auto; try lia. }
        assert (forall i, i < k -> is_cipher_of (ν 0) q (phi i) (pi i)) as Hpi.
        { unfold pi; intros i Hi.
          destruct (lt_eq_lt_dec i k) as [ [H | ] | ]; try lia.
          apply (proj2_sig (the_cipher (phi i) Hq (fun j Hj => Hphi1 _ _ H Hj))). }
        assert (Hpi_q : pi iq = q).
        { unfold pi; destruct (lt_eq_lt_dec iq k) as [ [H | ] | ]; try lia. }
        generalize pi Hpi_k Hpi_q Hpi; clear pi Hpi_k Hpi Hpi_q.
        intros pi Hpi_k Hpi_q Hpi; subst u.

        exists pi; red.
        rewrite ciphers_spec.
        destruct (le_lt_dec il k) as [ ? | _ ]; try lia.
        destruct (le_lt_dec il il) as [ _ | ? ]; try lia.
        destruct (le_lt_dec il iq) as [ ? | _ ]; try lia.
        rewrite Nat.sub_diag. 
        subst q; repeat (split; auto).
        * exists phi; intros i Hi.
          destruct (le_lt_dec il i); try lia; auto.
        * rewrite dc_list_Code_spec with (π := pi) (φ := phi); auto;
            intros i Hi; destruct (le_lt_dec il i); auto; lia.
    Qed.

    Let dc_list_bfall_spec ν : 
            (forall i, i < ν 0 -> exists φ, Forall (dc_eval φ i·ν) ll) 
        <-> dc_list_bfall ν.
    Proof.
      rewrite dc_list_bfall_spec_1; split.
      + intros H.
        apply fmmap_reifer_bound  with (p := k) in H.
        - destruct H as (m & phi & Hf).
          set (q := power (ν 0+2+m) 2).
          assert (ν 0+1 < q) as Hlq.
          { apply Nat.lt_le_trans with (ν 0+2+m); try lia.
            apply power_ge_n; auto. }
          assert (m <= power q 2) as Hmq.
          { apply Nat.le_trans with q.
            apply Nat.le_trans with (ν 0+2+m); try lia.
            apply power_ge_n; auto.
            apply power_ge_n; auto. }
          exists q, (fun i j => phi j i); split; [ | split ]; auto.
          * intros i j Hi Hj; apply Nat.lt_le_trans with m; auto; apply Hf; auto.
          * intros; apply Hf; auto.
        - intros x f g Hfg.
          apply Forall_impl.
          intros c Hc; apply dc_eval_ext; auto.
          intros z Hz; symmetry; apply Hfg, Hll with c; auto.
      + intros (q & phi & Hq & H1 & H2) j Hj.
        exists (fun i => phi i j); auto.
    Qed.

    Local Theorem dio_rel_dc_list_bfall : 𝔻R (fun ν => forall i, i < ν 0 -> exists φ, Forall (dc_eval φ i·ν) ll).
    Proof using Hll.
      dio by lemma dc_list_bfall_spec; unfold dc_list_bfall.
      destruct dio_rel_pre_quant as (f & Hf).
      exists (df_mexists il f).
      abstract (intros; rewrite df_mexists_spec; split;
        intros (phi & H); exists phi; revert H; rewrite <- Hf; auto).
    Defined.

  End dio_bounded_elem.

  Local Theorem dio_rel_bounded_fall R : 𝔻R R -> 𝔻R (fun ν => forall i, i < ν 0 -> R i·ν).
  Proof.
    intros (f & Hf).
    destruct (dio_formula_elem f) as (ll & H1 & H2 & H3).
    revert H2; generalize (4*df_size f); intros k H2.
    generalize (dio_rel_dc_list_bfall _ H2); apply dio_rel_equiv.
    abstract (intros v; split; intros H i Hi; generalize (H _ Hi); rewrite <- Hf, H3; auto).
  Defined.

End dio_rel_bounded_fall.

(* Composition and renaming to get the desired result, 
    ie Matiyasevich theorem of 1997 stating the 

      "Diophantine admissibility of
           bounded universal quantification" 

    ie bounded universal quantification is a 
    Diophantine shape
*)

Theorem dio_rel_fall_lt a (R : nat -> (nat -> nat) -> Prop) : 
           𝔻F a 
   -> 𝔻R (fun ν => R (ν 0) ν⭳) 
   -> 𝔻R (fun ν => forall x, x < a ν -> R x ν).
Proof.
  intros Ha H.
  by dio equiv (fun ν => exists y, y = a ν /\ forall x, x < y -> R x ν).
  + abstract(intros v; split; 
      [ exists (a v); auto
      | intros (? & -> & ?); auto ]).
  + set (T v := R (v 0) v⭳⭳).
    by dio equiv (fun v => forall x, x < v 0 -> T (x·v)).
    * abstract (intros v; unfold T; simpl; tauto).
    * apply dio_rel_bounded_fall; unfold T; simpl.
      revert H; apply dio_rel_ren 
        with (ρ := fun n => match n with 0 => 0 | S n => S (S n) end).
Defined.

#[export] Hint Resolve dio_rel_fall_lt : dio_rel_db.

(* Two variants *)

Corollary dio_rel_fall_lt_bound a (R : nat -> nat -> (nat -> nat) -> Prop) : 
           𝔻F a
   -> 𝔻R (fun ν => R (ν 0) (a ν⭳) ν⭳) 
   -> 𝔻R (fun ν => forall x, x < a ν -> R x (a ν) ν).
Proof. intros; dio auto. Defined.

Corollary dio_rel_fall_le a (R : nat -> (nat -> nat) -> Prop) : 
           𝔻F a
   -> 𝔻R (fun ν => R (ν 0) ν⭳) 
   -> 𝔻R (fun ν => forall x, x <= a ν -> R x ν).
Proof.
  intros Ha HK.
  by dio equiv (fun v => forall x, x < 1+a v -> R x v).
  abstract (intros v; split; intros H x Hx; apply H; lia).
Defined.

#[export] Hint Resolve dio_rel_fall_lt_bound 
             dio_rel_fall_le : dio_rel_db.
