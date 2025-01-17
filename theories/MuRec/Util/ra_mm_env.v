(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
  Require Import utils finite pos vec subcode sss.

From Undecidability.MinskyMachines 
  Require Import env mme_defs mme_utils. 

From Undecidability.MuRec.Util 
  Require Import recalg. 

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "P // s ->> t" := (sss_compute (mm_sss_env eq_nat_dec) P s t).
Local Notation "P // s -+> t" := (sss_progress (mm_sss_env eq_nat_dec) P s t).
Local Notation "P // s -[ k ]-> t" := (sss_steps (mm_sss_env eq_nat_dec) P k s t).
Local Notation "P // s ↓" := (sss_terminates (mm_sss_env eq_nat_dec ) P s). 

Local Notation " e ⇢ x " := (@get_env _ _ e x).
Local Notation " e ⦃  x ⇠ v ⦄ " := (@set_env _ _ eq_nat_dec e x v).
Local Notation "x '⋈' y" := (forall i : nat, x⇢i = y⇢i :> nat) (at level 70, no associativity).

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section ra_compiler.

  Ltac dest x y := destruct (eq_nat_dec x y) as [ | ]; [ subst x | ]; rew env.

  (* We compile f : recalg n 
      into (nat indexed) MM code at i where 
       a) inputs are indexed with registers between [p,p+n[, 
       b) output is indexed by o
       c) spare registers are indexed above m 

      Generally, the hypotheses 
       h0) o < m, 
       h1) n+p <= m, 
       h2) ~ p <= o < n+p
      are needed to ensure compilation is possible. They avoid
      clashes between inputs, output and spare registers 

      Doing so allows us great freedom in the choice of
      registers during compilation.

      The result should be MM code that simulates the computation
      of f from a state where spare registers value 0,
      and the only register that is allowed to be modified 
      is the output register
    *)

  Definition ra_compiled n (f : recalg n) i p o m (P : list (mm_instr nat)) :=
       forall v e, (forall i, m <= i -> e⇢i = 0) 
                -> (forall q, e⇢(pos2nat q+p) = vec_pos v q) 
                -> (forall x, ⟦f⟧ v x  
                   -> exists e', e' ⋈ e⦃o⇠x⦄
                              /\ (i,P) // (i,e) ->> (length P + i,e'))
                /\ ((i,P) // (i,e) ↓ -> exists x, ⟦f⟧ v x).

  Definition ra_compiler_spec n f i p o m := sig (@ra_compiled n f i p o m).

  Definition ra_compiler_stm n f :=
    forall i p o m, o < m
                 -> ~ p <= o < n+p
                 -> n+p <= m
                 -> @ra_compiler_spec n f i p o m.

  Hint Resolve sss_progress_compute : core.

  Fact ra_compiler_cst c : ra_compiler_stm (ra_cst c). 
  Proof.
    red; simpl; intros i p o m H1 H2 H3.
    exists (mm_set o m c i); intros v e H4 _; split.
    2: exists c; cbv; auto.
    revert H4; vec nil v; clear v.
    intros H4 x E; simpl in E; subst x.
    rewrite mm_set_length.
    destruct mm_set_progress 
      with (dst := o) (zero := m) (n := c) (i := i) (e := e)
      as (e' & G1 & G2); auto; try lia.
    exists e'; split; auto.
  Qed.

  Fact ra_compiler_zero : ra_compiler_stm ra_zero. 
  Proof.
    red; simpl; intros i p o m H1 H2 H3.
    exists (mm_set o m 0 i); intros v e H4 H5; split.
    2: exists 0; cbv; auto.
    intros x; revert H5.
    vec split v with a; vec nil v; clear v.
    intros H5 E; cbv in E; subst x.
    rewrite mm_set_length.
    destruct mm_set_progress 
      with (dst := o) (zero := m) (n := 0) (i := i) (e := e)
      as (e' & G1 & G2); auto; try lia.
    exists e'; split; auto.
  Qed.

  Fact ra_compiler_succ : ra_compiler_stm ra_succ.
  Proof.
    red; simpl; intros i p o m H1 H2 H3.
    exists (mm_copy p o m (m+1) i ++ INC o :: nil); 
      intros v e H4 H5; split.
    2: exists (S (vec_head v)); cbv; auto.
    intros x; revert H5; vec split v with a; vec nil v; clear v.
    intros H5 H; simpl in H; subst x.
    specialize (H5 pos0); rewrite pos2nat_fst in H5; simpl in H5.
    destruct mm_copy_progress 
      with (src := p) (dst := o) (tmp := m) (zero := m+1) (i := i) (e := e)
      as (e' & H7 & H8); try lia; try (apply H4; lia).
    exists (e'⦃o⇠S a⦄); split.
    * intros j; dest j o; rewrite H7; rew env.
    * rew length. 
      apply sss_compute_trans with (9+i, e').
      - apply sss_progress_compute.
        revert H8; apply subcode_sss_progress; auto.
      - mm env INC with o.
        mm env stop.
        rewrite H7, H5; rew env.
  Qed.

  Fact ra_compiler_proj n q : ra_compiler_stm (@ra_proj n q).
  Proof.
    red; simpl; intros i p o m H1 H2 H3.
    exists (mm_copy (pos2nat q+p) o m (m+1) i); 
      intros v e H4 H5; split.
    2: exists (vec_pos v q); cbv; auto.
    intros x E; simpl in E; subst x.
    destruct mm_copy_progress 
      with (src := pos2nat q+p) (dst := o) (tmp := m) (zero := m+1) (i := i) (e := e)
      as (e' & H7 & H8); try lia; try (apply H4; lia);
        try (generalize (pos2nat_prop q); lia).
    exists e'; split.
    * intros j; rewrite H7; dest j o.
    * rew length; apply sss_progress_compute; auto.
  Qed.

  Section ra_compiler_comp.

    Variable (n : nat).

    Local Fact ra_compiler_vec k (g : vec (recalg n) k) : 
           (forall p, ra_compiler_stm (vec_pos g p))
        -> forall i p o m,  
                    o+k <= m
                 -> n+p <= o
                 -> { P : list (mm_instr nat) |
       (forall v w e, (forall q, ⟦vec_pos g q⟧ v (vec_pos w q)) 
                   -> (forall i, m <= i -> e⇢i = 0)
                   -> (forall j, e⇢(pos2nat j+p) = vec_pos v j) 
                   -> exists e', (forall j, ~ o <= j < o+k -> e'⇢j = e⇢j)
                              /\ (forall q, e'⇢(pos2nat q+o) = vec_pos w q)
                              /\ (i,P) // (i,e) ->> (length P + i,e')) 
      /\ (forall v e, (i,P) // (i,e) ↓
                   -> (forall i, m <= i -> e⇢i = 0)
                   -> (forall q, e⇢(pos2nat q+p) = vec_pos v q) 
                   -> (forall q, exists x, ⟦vec_pos g q⟧ v x)) }.
    Proof.
      induction g as [ | k f g IHg ]; intros Hg i p o m H1 H2.
      + exists nil; split.
        2: intros v e H3 H4 H5 q; analyse pos q.
        intros v w e; vec nil w; clear w.
        intros _ H3 H4.
        exists e; split; [ | split ]; auto.
        * intros q; analyse pos q.
        * simpl; mm env stop.
      + destruct (Hg pos0) with (i := i) (p := p) (o := o) (m := m)
          as (P & HP); try lia.
        destruct IHg with (i := length P+i) (p := p) (o := S o) (m := m)
          as (Q & HQ1 & HQ2); try lia.
        { intros q; apply (Hg (pos_nxt q)). }
        exists (P++Q); split.
        * intros v w e; vec split w with a. 
          intros H3 H4 H5.
          generalize (H3 pos0) (fun q => H3 (pos_nxt q)); clear H3; intros H6 H7.
          simpl in H6, H7.
          destruct (proj1 (HP v e H4 H5) a) as (e1 & G1 & G2); auto.
          destruct (HQ1 v w e1) as (e2 & G3 & G4 & G5); auto.
          { intros j Hj; rewrite G1; dest j o; lia. }
          { intros q; rewrite G1.
            assert (pos2nat q+p <> o); try rew env.
            generalize (pos2nat_prop q); lia. }
          exists e2; split; [ | split ].
          - intros j Hj.
            rewrite G3, G1; try lia.
            dest j o; lia.
          - intros q; analyse pos q; simpl.
            ++ rewrite pos2nat_fst, G3, G1; try lia.
               simpl; rew env.
            ++ rewrite pos2nat_nxt, <- G4; f_equal; lia.
          - apply sss_compute_trans with (length P+i,e1).
            ++ revert G2; apply subcode_sss_compute; auto.
            ++ rew length.
               revert G5; rewrite Nat.add_assoc, (Nat.add_comm _ (length _)).
               apply subcode_sss_compute.
               subcode_tac; rewrite app_nil_r; auto.
        * intros v e H3 H4 H5.
          assert ((i,P) // (i,e) ↓) as H6.
          { apply subcode_sss_terminates with (2 := H3); auto. }
          destruct (proj2 (HP v _ H4 H5)) with (1 := H6) as (a & Ha); auto.
          simpl in Ha.
          destruct (proj1 (HP _ _ H4 H5) _ Ha) as (e1 & G1 & G2); auto.
          intros q; analyse pos q; simpl.
          1: exists a; auto.
          apply HQ2 with e1.
          - assert ((i,P++Q) // (length P+i,e1) ↓) as H7.
            { apply subcode_sss_terminates_inv 
               with (2 := H3) (P := (i,P)) (st1 := (length P+i,e1)); auto.
             * apply mm_sss_env_fun.
             * split; simpl; auto; lia. }
            destruct H7 as (st & H7 & H8).
            assert ( (length P+i,Q) <sc (i,P++Q) ) as H9.
            { subcode_tac; rewrite app_nil_r; auto. }
            destruct subcode_sss_compute_inv 
              with (P := (length P+i,Q)) (3 := H7)
              as (st2 & F1 & _ & F2); auto.
            { revert H8; apply subcode_out_code; auto. }
            exists st2; split; auto.
          - intros j Hj; rewrite G1; dest j o; lia.
          - clear q; intros q; rewrite G1.
            assert (pos2nat q+p <> o); try rew env.
            generalize (pos2nat_prop q); lia.
    Qed.

    Variable (k : nat) (f : recalg k) (g : vec (recalg n) k)
             (Hf : ra_compiler_stm f)
             (Hg : forall q, ra_compiler_stm (vec_pos g q)).

    (* compile (g[0])   input [p,p+n[   output m+0      spare m+k
       compile (g[1])   input [p,p+n[   output m+1      spare m+k
       ...
       compile (g[k-1]) input [p,p+n[   output m+k-1    spare m+k
       compile f        input [m,m+k[   output o        spare m+k
       mm_multi_erase (m+k) (list_an m k) ...

     *)

    Fact ra_compiler_comp : ra_compiler_stm (ra_comp f g).
    Proof using Hf Hg.
      red; simpl; intros i p o m H1 H2 H3.
      destruct ra_compiler_vec with (1 := Hg) (i := i) (p := p) (o := m) (m := m+k)
        as (P & HP1 & HP2); auto.
      destruct Hf with (i := length P+i) (p := m) (o := o) (m := m+k)
        as (Q & HQ); try lia; auto.
      exists (P++Q++mm_multi_erase m (k+m) k (length P+length Q+i)); 
        intros v e H6 H7; split.
      + intros x; simpl; intros (w & H4 & H8).
        assert (forall q, ⟦vec_pos g q⟧ v (vec_pos w q)) as H5.
        { intros q; generalize (H8 q); rewrite vec_pos_set; auto. }
        clear H8.
        destruct (HP1 v w e) as (e1 & G1 & G2 & G3); auto.
        { intros; apply H6; lia. }
        destruct (HQ w e1) as [ HQ1 _ ]; auto.
        { intros j Hj; rewrite G1, H6; lia. }
        destruct (HQ1 x) as (e2 & G4 & G5); auto.
        destruct mm_multi_erase_compute 
          with (zero := k+m) (dst := m) (k := k) (i := length P+length Q+i) (e := e2)
          as (e3 & G6 & G7 & G8); try lia; auto.
        { rewrite G4, get_set_env_neq, G1, H6; lia. }
        exists e3; split.
        * intros j.
          destruct (interval_dec m (k+m) j) as [ H | H ].
          - rewrite G6, get_set_env_neq, H6; lia.
          - rewrite G7, G4; try lia; dest j o.
            apply G1; lia.
        * rew length.
          apply sss_compute_trans with (length P+i,e1).
          { revert G3; apply subcode_sss_compute; auto. }
          apply sss_compute_trans with (length P+length Q+i,e2).
          { revert G5; rewrite Nat.add_assoc, (Nat.add_comm _ (length _)).
            apply subcode_sss_compute; auto. }
          replace (length P+(length Q+2*k)+i) 
            with  (2*k+(length P+length Q+i)) by lia.
          revert G8; apply subcode_sss_compute; auto.
    + intros H4.
      assert ((i,P) // (i,e) ↓) as H5.
      { revert H4; apply subcode_sss_terminates; auto. }
      assert (forall q, ex (⟦vec_pos g q⟧ v)) as H8. 
      { apply HP2 with (1 := H5) (3 := H7).
        intros; apply H6; lia. }
      apply vec_reif in H8; destruct H8 as (w & Hw).
      destruct (HP1 v w e) as (e1 & G1 & G2 & G3); auto.
      { intros; apply H6; lia. }
      destruct (HQ w e1) as [ _ (x & Hx) ]; auto.
        { intros j Hj; rewrite G1, H6; lia. }
      - apply subcode_sss_terminates 
          with (Q := (i,P++Q++mm_multi_erase m (k + m) k (length P+length Q+i))); auto.
        apply subcode_sss_terminates_inv with (2 := H4) (P := (i,P)); auto.
        { apply mm_sss_env_fun. }
        split; simpl; auto; lia.
      - exists x, w; split; auto.
        intros q; rewrite vec_pos_set; auto.
    Qed.

  End ra_compiler_comp.

  Section ra_compiler_rec.

    Variables (n : nat) (f : recalg n) (g : recalg (S (S n)))
              (Hf : ra_compiler_stm f)
              (Hg : ra_compiler_stm g).

    (* i p o m 
             
              input = v0##<v>
              
              p : v0
              [p+1,p+n] : v

              m+0 : 0,...,v0
              m+1 : g^_(f v)
              [m+2,m+n+1] : <v>
              m+n+1 : v0,v0-1,....,0
              m+n+2 : 0 (zero)
              m+n+3 : 0 (tmp)
             
    i:         copy [1+p,n+S p[ -> [m+2,n+m+2[
    9n+i:      copy p           -> m+n+1
    9+9n+i:    erase  m (utiliser m pour zero)
   11+9n+i:    compile f ? (3+m) o (3+n+m)
  11+l1+9n+i:  DEC p sauter vers 23+l1+l2+9n+i
  12+l1+9n+i:  copier o -> m+1
  21+l1+9n+i:  compile g ? m o (3+n+m)
21+l1+l2+9n+i: INC m+1
22+l1+l2+9n+i: DEC zero jmp (11+l1+9n+i)
23+l1+l2+9n+i: efface [m+1,3+n+m[

      *)

    Variables (i p o m : nat)
              (H1 : o < m) 
              (H2 : ~ p <= o < S (n + p))
              (H3 : S (n + p) <= m).

    Notation v0   := (2+n+m).
    Notation zero := (3+n+m).
    Notation tmp  := (4+n+m).

    Local Definition rec_Q1 := 
              mm_multi_copy tmp zero n (1+p) (2+m) i
           ++ mm_copy p v0 tmp zero (9*n+i)
           ++ mm_erase m zero (9+9*n+i).

    Notation Q1 := rec_Q1.

    Local Fact rec_Q1_length : length Q1 = 11+9*n.
    Proof using H1 H2 H3. unfold Q1; rew length; lia. Qed.

    Local Fact rec_F_full : ra_compiler_spec f (11+9*n+i) (2+m) o zero.
    Proof using Hf H1 H2 H3. apply Hf; lia. Qed.

    Notation F := (proj1_sig rec_F_full).
    Local Definition rec_HF1 x v e H1 H2 := proj1 (proj2_sig rec_F_full v e H1 H2) x.
    Local Definition rec_HF2 v e H1 H2 := proj2 (proj2_sig rec_F_full v e H1 H2).

    Local Fact rec_G_full : ra_compiler_spec g (21+length F+9*n+i) m o zero.
    Proof using Hg H1 H2 H3. apply Hg; lia. Qed.

    Notation G := (proj1_sig rec_G_full).
    Local Definition rec_HG1 x v e H1 H2 := proj1 (proj2_sig rec_G_full v e H1 H2) x.
    Local Definition rec_HG2 v e H1 H2 := proj2 (proj2_sig rec_G_full v e H1 H2).

    Local Definition rec_s2 := 11+length F+9*n+i.

    Notation s2 := rec_s2.

    Local Definition rec_Q2 := 
              DEC v0 (23+length F+length G+9*n+i)
           :: mm_copy o (1+m) tmp zero (12+length F+9*n+i)
           ++ G
           ++ INC m :: DEC zero rec_s2 :: nil.

    Notation Q2 := rec_Q2.

    Local Fact rec_Q2_progress_O e :
               e⇢v0 = 0
            -> (s2,Q2) // (s2,e) -+> (length Q2+s2,e).
    Proof.
      intros G1.
      unfold Q2.
      mm env DEC zero with v0 (23+length F+length G+9*n+i).
      mm env stop; f_equal; rew length.
      unfold s2; lia.
    Qed.

    Local Fact rec_Q2_progress_S x y v e :
              (forall j, zero <= j -> e⇢j = 0)
           -> (forall j, vec_pos v j = e⇢(pos2nat j+2+m))
           -> e⇢v0 = S x
           -> ⟦g⟧ (e⇢m##e⇢o##v) y
           -> exists e', (forall j, j <> o -> j <> v0 -> j <> m -> j <> 1+m -> e'⇢j = e⇢j)
                      /\ e'⇢o = y
                      /\ e'⇢v0 = x
                      /\ e'⇢m = S (e⇢m) 
                      /\ e'⇢(1+m) = e⇢o
                      /\ (s2,Q2) // (s2,e) -+> (s2,e').
    Proof.
      generalize rec_Q1_length; intros Q1_length.
      intros G1 G2 G3 G4.
      set (e1 := e⦃v0⇠x⦄).
      destruct (@mm_copy_progress o (1+m) tmp zero) 
        with (i := 12+length F+9*n+i) (e := e1)
        as (e2 & G5 & G6); try lia.
      1,2: unfold e1; rewrite get_set_env_neq, G1; lia.
      destruct rec_HG1 with (e := e2) (3 := G4)
        as (e3 & G7 & G8).
      { intros j Hj; rewrite G5; unfold e1.
        dest j (1+m); try lia.
        dest j (2+n+m); try lia. }
      { intros j.
        rewrite G5; unfold e1.
        analyse pos j.
        * rewrite pos2nat_fst; simpl.
          do 2 (rewrite get_set_env_neq; try lia).
        * rewrite pos2nat_nxt, pos2nat_fst; rew env.
          rewrite get_set_env_neq; auto; lia.
        * do 2 rewrite pos2nat_nxt.
          generalize (pos2nat_prop j); intro Hj.
          do 2 (rewrite get_set_env_neq; try lia).
          simpl; rewrite G2; f_equal; lia. }
      exists (e3⦃m⇠S(e⇢m)⦄); msplit 5.
      * intros j F1 F2 F3 F4; rew env.
        rewrite G7; rew env.
        rewrite G5; unfold e1; rew env.
      * rewrite get_set_env_neq, G7; try lia; rew env.
      * rewrite get_set_env_neq, G7; try lia.
        rewrite get_set_env_neq, G5; try lia.
        unfold e1; rewrite get_set_env_neq; try lia.
        rew env.
      * rew env.
      * rewrite get_set_env_neq, G7; try lia.
        rewrite get_set_env_neq, G5; try lia.
        rew env; unfold e1.
        rewrite get_set_env_neq; lia.
      * unfold Q2.
        mm env DEC S with v0 (23 + length F + length G + 9 * n + i) x.
        apply sss_compute_trans with (21+length F+9*n+i,e2).
        { apply sss_progress_compute.
          unfold s2, Q2; revert G6; apply subcode_sss_progress; auto. }
        apply sss_compute_trans with (length G+(21+length F+9*n+i), e3).
        { unfold s2, Q2; revert G8; apply subcode_sss_compute; auto. }
        mm env INC with m.
        { unfold s2; subcode_tac. }
        mm env DEC zero with zero s2.
        { unfold s2; subcode_tac. }
        { rewrite get_set_env_neq; try lia.
          rewrite G7, get_set_env_neq; try lia.
          rewrite G5, get_set_env_neq; try lia.
          unfold e1; rewrite get_set_env_neq; try lia.
          apply G1; lia. }
        mm env stop; do 3 f_equal.
        rewrite G7, get_set_env_neq; try lia.
        rewrite G5, get_set_env_neq; try lia.
        unfold e1; rewrite get_set_env_neq; lia.
    Qed.

    Local Fact rec_Q2_progress_S_inv x v e :
              (forall j, zero <= j -> e⇢j = 0)
           -> (forall j, vec_pos v j = e⇢(pos2nat j+2+m))
           -> e⇢v0 = S x
           -> (s2,Q2) // (s2,e) ↓
           -> exists y, ⟦g⟧ (e⇢m##e⇢o##v) y.
    Proof.
      intros G1 G2 G3 ((s & e') & (k & G4) & G5).
      unfold fst in G5.
      assert (G6 : exists e1, e1 ⋈  e⦃v0⇠x⦄⦃1+m⇠(e⇢o)⦄
                           /\ (s2,Q2) // (s2,e) -+> (10+s2,e1)).
      { destruct mm_copy_progress 
          with (src := o) (dst := 1+m) (tmp := tmp) (zero := zero) 
               (i := 12+length F+9*n+i) (e := e⦃v0⇠x⦄)
          as (e2 & G6 & G7); try lia.
        1,2: rewrite get_set_env_neq, G1; lia.
        exists e2; split.
        + intros j; rewrite G6; auto.
          rewrite get_set_env_neq with (q := o); auto; lia.
        + unfold Q2.
          mm env DEC S with v0 (23+length F+length G+9*n+i) x.
          replace (1+s2) with (12+length F+9*n+i) by (unfold s2; lia).
          replace (10+s2) with (9+(12+length F+9*n+i)) by (unfold s2; lia).
          apply sss_progress_compute.
          revert G7; apply subcode_sss_progress; auto.
          unfold s2; subcode_tac. }
      destruct G6 as (e1 & G6 & G7).
      destruct subcode_sss_progress_inv with (4 := G7) (5 := G4)
        as (k' & G8 & G9); auto.
      { apply mm_sss_env_fun. }
      { apply subcode_refl. }
      apply rec_HG2 with (e := e1).
      * intros j Hj; rewrite G6, get_set_env_neq, get_set_env_neq; auto; lia.
      * intros j; rewrite G6; analyse pos j.
        + rewrite pos2nat_fst; simpl. 
          do 2 (rewrite get_set_env_neq; try lia).
        + rewrite pos2nat_nxt, pos2nat_fst; rew env.
        + do 2 rewrite pos2nat_nxt; simpl.
          generalize (pos2nat_prop j); intros G10.
          do 2 (rewrite get_set_env_neq; try lia).
          rewrite G2; f_equal; lia.
      * apply subcode_sss_terminates with (Q := (s2,Q2)).
        + unfold Q2, s2; auto.
        + exists (s,e'); split; auto.
          exists k'; apply G9.
    Qed.
 
    Local Fact rec_Q2_compute_rec (v : vec nat n) e s k :
              (forall j, zero <= j -> e⇢j = 0)
           -> (forall j, vec_pos v j = e⇢(pos2nat j+2+m))
           -> e⇢o = s 0
           -> e⇢v0 = k
           -> (forall i, i < k -> ⟦g⟧ (i+(e⇢m)##s i##v) (s (S i)))
  -> exists e', (forall j, j <> o -> j <> v0 -> j <> m -> j <> 1+m -> e'⇢j = e⇢j)
             /\ e'⇢o     = s k
             /\ e'⇢v0    = 0
             /\ e'⇢m     = (e⇢v0)+(e⇢m)
             /\ (s2,Q2) // (s2,e) -+> (length Q2+s2,e').
    Proof.
      revert e s; induction k as [ | k IHk ]; intros e s G1 G2 G3 G4 G5.
      + exists e; msplit 4; auto. 
        * rewrite G4; auto.
        * apply rec_Q2_progress_O; auto.
      + generalize (G5 0); intros G6; spec in G6; try lia.
        rewrite <- G3 in G6; simpl in G6.
        destruct rec_Q2_progress_S with (3 := G4) (4 := G6)
          as (e1 & F1 & F2 & F3 & F4 & F5 & F6); auto.
        destruct IHk with (s := fun i => s (S i)) (e := e1)
          as (e2 & T1 & T2 & T3 & T4 & T5); auto.
        * intros; rewrite F1, G1; lia.
        * intros j; generalize (pos2nat_prop j); intro.
          rewrite F1, G2; auto; lia.
        * intros j Hj.
          rewrite F4.
          replace (j+S(e⇢m)) with ((S j)+(e⇢m)) by lia. 
          apply G5; lia.
        * exists e2; msplit 4; auto.
          - intros j ? ? ? ?; rewrite T1; auto.
          - rewrite T4, F3, F4, G4; lia.
          - apply sss_progress_trans with (1 := F6); auto.
    Qed.

    Local Fact rec_Q2_compute_rev (v : vec nat n) e  :
              (forall j, zero <= j -> e⇢j = 0)
           -> (forall j, vec_pos v j = e⇢(pos2nat j+2+m))
           -> (s2,Q2) // (s2,e) ↓
           -> exists s, s 0 = e⇢o /\ forall i, i < e⇢v0 -> ⟦g⟧ (i+(e⇢m)##s i##v) (s (S i)).
    Proof.
      intros G1 G2 ((u & e') & (k & G3) & G4).
      unfold fst in G4.
      revert e e' G1 G2 G3 G4.
      induction on k as IHk with measure k.
      intros e e' G1 G2 G3 G0.
      case_eq (e⇢v0).
      + intros ?; exists (fun _ => e⇢o); split; auto; intros; lia.
      + intros x Hx.
        destruct rec_Q2_progress_S_inv 
          with (1 := G1) (2 := G2) (3 := Hx)
          as (y & Hy).
        { exists (u,e'); split; auto; exists k; auto. }
        destruct rec_Q2_progress_S with (3 := Hx) (4 := Hy)
          as (e1 & G4 & G5 & G6 & G7 & G8 & G9); auto.
        destruct subcode_sss_progress_inv with (4 := G9) (5 := G3)
          as (k' & F1 & F2); auto.
        { apply mm_sss_env_fun. }
        { apply subcode_refl. }
        apply IHk in F2; auto.
        * destruct F2 as (s & Hs1 & Hs2).
          exists (fun i => match i with 0 => e⇢o | S i => s i end); split; auto.
          intros [ | j ] Hj; simpl.
          - rewrite Hs1, G5; auto.
          - specialize (Hs2 j).
            rewrite G7 in Hs2.
            replace (S (j+(e⇢m))) with (j+S(e⇢m)) by lia.
            apply Hs2; lia.
        * intros j Hj; rewrite G4, G1; lia.
        * intros j; rewrite G2, G4; try lia.
          generalize (pos2nat_prop j); intro; lia.
    Qed.

    Local Fact rec_Q2_length : length Q2 = 12+length G.
    Proof. unfold Q2; rew length; ring. Qed.

    Local Definition rec_Q3 := mm_multi_erase m zero (2+n) (23+length F+length G+9*n+i).

    Notation Q3 := rec_Q3.

    Local Fact rec_Q3_length : length Q3 = 4+2*n.
    Proof. unfold Q3; rew length; ring. Qed.
    
    Local Fact rec_Q1_progress e :
                (forall j, zero <= j -> e⇢j = 0)
  -> exists e', (forall j, j < n -> e'⇢(j+2+m) = e⇢(j+1+p))
             /\ e'⇢v0 = e⇢p  
             /\ e'⇢m = 0 
             /\ (forall j, j <> m -> ~ 2+m <= j <= v0 -> e'⇢j = e⇢j)
             /\ (i,Q1) // (i,e) -+> (length Q1+i,e').
    Proof using H1 H2 H3.
      intros G3.
      destruct (@mm_multi_copy_compute tmp zero n (1+p) (2+m))
        with (i := i) (e := e) 
        as (e1 & G4 & G5 & G6); try lia.
      1,2: apply G3; lia.
      destruct (@mm_copy_progress p v0 tmp zero) 
        with (i := 9*n+i) (e := e1) 
        as (e2 & G7 & G8); try lia.
      1,2: rewrite G5, G3; lia.
      destruct (@mm_erase_progress m zero)
        with (i := 9+9*n+i) (e := e2)
        as (e3 & G9 & G10); try lia.
      1: rewrite G7, get_set_env_neq, G5, G3; lia.
      exists e3; msplit 4.
      * intros j Hj.
        rewrite G9, get_set_env_neq,
                G7, get_set_env_neq, 
                <- Nat.add_assoc, G4; try lia.
        f_equal; lia.
      * rewrite G9, get_set_env_neq, G7; rew env; try lia.
        rewrite G5; lia.
      * rewrite G9; rew env.
      * intros j Hj1 Hj2.
        rewrite G9; rew env.
        rewrite G7, get_set_env_neq, G5; lia.
      * rewrite rec_Q1_length; unfold Q1.
        apply sss_compute_progress_trans with (9*n+i,e1).
        { revert G6; apply subcode_sss_compute; auto. }
        apply sss_progress_trans with (9+(9*n+i), e2).
        { revert G8; apply subcode_sss_progress; auto. }
        { rewrite Nat.add_assoc; revert G10.
          apply subcode_sss_progress; auto. }
    Qed.

    Notation Q4 := (Q1++F++Q2++Q3).

    Local Fact rec_Q4_progress (v : vec nat (S n)) x e :
                 (forall j, m <= j -> e⇢j = 0)
              -> (forall j, vec_pos v j = e⇢(pos2nat j+p))
              -> s_rec ⟦f⟧ ⟦g⟧ v x
  -> exists e', (forall j, j <> o -> e'⇢j = e⇢j)
              /\ e'⇢o     = x
              /\ (i,Q4) // (i,e) -+> (length Q4+i,e').
    Proof.
      generalize rec_Q1_length rec_Q2_length rec_Q3_length.
      intros Q1_length Q2_length Q3_length.
      vec split v with k.
      intros G1 G2 G3.
      rewrite s_rec_eq in G3.
      destruct G3 as (s & G3 & G4 & G5); simpl vec_head in *; simpl vec_tail in *.
      generalize (G2 pos0); rewrite pos2nat_fst; intros G0; simpl in G0.
      generalize (fun j => G2 (pos_nxt j)); clear G2; intros G2; simpl in G2.
      destruct rec_Q1_progress with (e := e) as (e1 & F1 & F2 & F3 & F4 & F5).
      { intros; apply G1; lia. }
      assert (forall j, e1 ⇢ pos2nat j + (2 + m) = vec_pos v j) as G6.
      { intros j; rewrite G2, pos2nat_nxt.
        replace (S (pos2nat j)+p) with (pos2nat j+1+p) by lia.
        generalize (pos2nat_prop j); intros H.
        rewrite <- F1; auto; f_equal; lia. }
      destruct rec_HF1 with (3 := G3) (e := e1) as (e2 & F6 & F7); auto.
      { intros j Hj; rewrite F4, G1; lia. }
      destruct rec_Q2_compute_rec with (e := e2) (v := v) (s := s) (k := k)
        as (e3 & F10 & F11 & F12 & _ & F14).
      { intros j Hj; rewrite F6, get_set_env_neq, F4, G1; lia. }
      { intros j; rewrite <- G6, F6, get_set_env_neq; try lia.
        f_equal; lia. }
      { rewrite F6; rew env. }
      { rewrite F6, get_set_env_neq, F2; lia. }
      { intros j Hj.
        rewrite F6, get_set_env_neq, F3, Nat.add_comm; try lia.
        simpl; apply G5; auto. }
      destruct mm_multi_erase_compute 
        with (zero := zero) (dst := m) (k := 2+n) (e := e3)
             (i := 23+length F+length G+9*n+i)
        as (e4 & F20 & F21 & F22); try lia.
      { rewrite F10, F6, get_set_env_neq, F4, G1; lia. }
      exists e4; msplit 2.
      * intros j Hj.
        dest j (2+n+m).
        { rewrite F21, F12, G1; lia. }
        destruct (interval_dec m v0 j).
        - rewrite F20, G1; lia.
        - rewrite F21, F10, F6, get_set_env_neq, F4; try lia.
      * rewrite F21; try lia.
      * rew length.
        apply sss_progress_trans with (length Q1+i,e1).
        { revert F5; apply subcode_sss_progress; auto. }
        apply sss_compute_progress_trans with (length F+length Q1+i,e2).
        { rewrite Q1_length.
          replace (length F+(11+9*n)+i) with (length F+(11+9*n+i)) by lia.
          revert F7; apply subcode_sss_compute; auto. }
        apply sss_progress_compute_trans with (length Q2+s2,e3).
        { replace (length F+length Q1+i) with s2.
          revert F14; apply subcode_sss_progress; unfold s2; auto.
          unfold s2; rewrite Q1_length; lia. }
        { replace (length Q2+s2) with (23+length F+length G+9*n+i).
          replace (length Q1+(length F+(length Q2+length Q3))+i)
             with (2*(2+n)+(23+length F+length G+9*n+i)).
          revert F22; apply subcode_sss_compute; auto.
          unfold Q3; subcode_tac; rewrite app_nil_r; auto.
          rewrite Q1_length, Q2_length, Q3_length; lia.
          rewrite Q2_length; unfold s2; lia. }
    Qed.

    Local Fact rec_Q4_compute_rev (v : vec nat (S n)) e :
                 (forall j, m <= j -> e⇢j = 0)
              -> (forall j, vec_pos v j = e⇢(pos2nat j+p))
              -> (i,Q4) // (i,e) ↓
              -> exists x, s_rec ⟦f⟧ ⟦g⟧ v x.
    Proof.
      generalize rec_Q1_length rec_Q2_length rec_Q3_length.
      intros Q1_length Q2_length Q3_length.
      vec split v with k.
      intros G1 G2 G3.
      destruct rec_Q1_progress with (e := e)
        as (e1 & G4 & G5 & G6 & G7 & G8); auto.
      { intros; apply G1; lia. }
      generalize G3; intros G0.
      apply subcode_sss_terminates_inv 
        with (P := (i,Q1)) (st1 := (length Q1+i,e1)) in G3; auto.
      2: apply mm_sss_env_fun.
      2: { split.
           + apply sss_progress_compute; auto.
           + unfold out_code, code_end, fst, snd; lia. }
      assert (G9 : forall q : pos n, e1 ⇢ pos2nat q + (2 + m) = vec_pos v q).
      { intros j; specialize (G2 (pos_nxt j)); simpl in G2.
        rewrite G2, pos2nat_nxt, Nat.add_assoc, G4.
        + f_equal; lia.
        + apply pos2nat_prop. }
      destruct rec_HF2 with (v := v) (e := e1)
        as (x & Hx); auto.
      { intros j Hj; rewrite G7, G1; lia. }
      { rewrite Q1_length in G3.
        revert G3; apply subcode_sss_terminates; auto. }
      destruct rec_HF1 with (3 := Hx) (e := e1)
        as (e2 & F1 & F2); auto.
      { intros j Hj; rewrite G7, G1; lia. }
      destruct rec_Q2_compute_rev with (v := v) (e := e2)
        as (s & Hs1 & Hs2).
      { intros j Hj; rewrite F1, get_set_env_neq, G7, G1; lia. }
      { intros j; rewrite <- G9, F1, get_set_env_neq.
        + f_equal; lia.
        + lia. }
      { apply subcode_sss_terminates with (i, Q4).
        1: unfold s2; auto.
        apply subcode_sss_terminates_inv with (P := (i,Q1++F)) (2 := G3); auto.
        1: apply mm_sss_env_fun.
        1: rewrite app_assoc; apply subcode_left; auto.
        split.
        + rewrite Q1_length.
          replace s2 with (length F+(11+9*n+i)).
          revert F2; apply subcode_sss_compute; auto.
          unfold s2; lia.
        + unfold out_code, code_end, fst, snd.
          rew length; rewrite Q1_length; unfold s2; lia. }
      assert (k = e2⇢v0) as Hk.
      { rewrite F1, get_set_env_neq; try lia.
        rewrite G5; apply (G2 pos0). }
      exists (s k).
      apply s_rec_eq; exists s; msplit 2; auto.
      * simpl; rewrite Hs1, F1; rew env.
      * simpl; rewrite Hk; intros j Hj.
        specialize (Hs2 j Hj).
        rewrite F1, get_set_env_neq, G6, Nat.add_comm in Hs2; auto; lia.
    Qed.

    Fact ra_compiler_rec : ra_compiler_spec (ra_rec f g) i p o m.
    Proof using Hf Hg H1 H2 H3.
      exists Q4; intros v e G2 G3; split.
      + intros x; simpl ra_rel; intros G1.
        destruct rec_Q4_progress with (3 := G1) (e := e)
          as (e' & G4 & G5 & G6); auto.
        exists e'; split.
        * intros j; dest j o.
        * apply sss_progress_compute; auto.
      + intros G1.
        apply rec_Q4_compute_rev with (e := e); auto.
    Qed.

  End ra_compiler_rec.

  Section ra_compiler_min.

    Variables (n : nat) (f : recalg (S n)) (Hf : ra_compiler_stm f).

    (* i p o m 
             
              input = <v>
              
              [p,p+n[ : v

              m+0 : 0,1,...,
              [m+1,m+n] : <v>
              m+n+1 : 0 (zero)
              m+n+2 : 0 (tmp)
             
           i:  copy [p,p+n[ -> [m+1,n+m+1[
        9n+i:  erase  m 
      2+9n+i:  compile f ? m o zero
   2+l1+9n+i:  DEC o sauter vers ?
   3+l1+9n+i:  INC m
   4+l1+9n+i:  DEC zero jmp (2+9n+i)
   5+l1+9n+i:  copy m -> o
  14+l1+9n+i:  efface [m,n+m]

    *)

    Variables (i p o m : nat)
              (H1 : o < m) 
              (H2 : ~ p <= o < n + p)
              (H3 : n + p <= m).

    Notation zero := (1+n+m).
    Notation tmp  := (2+n+m).

    Local Definition min_Q1 := 
              mm_multi_copy tmp zero n p (1+m) i
           ++ mm_erase m zero (9*n+i).

    Notation Q1 := min_Q1.

    Local Fact min_Q1_length : length Q1 = 2+9*n.
    Proof using H1 H2 H3. unfold Q1; rew length; lia. Qed.

    Local Definition min_s1 := length Q1 + i.

    Notation s1 := min_s1.

    Local Fact min_F_full : ra_compiler_spec f s1 m o zero.
    Proof using Hf H1 H2 H3. apply Hf; lia. Qed.

    Notation F := (proj1_sig min_F_full).
    Local Definition min_HF1 x v e H1 H2 H3 := proj1 (proj2_sig min_F_full v e H2 H3) x H1.
    Local Definition min_HF2 v e H1 H2 H3 := proj2 (proj2_sig min_F_full v e H2 H3) H1.

    Local Definition min_Q2 := 
              F
           ++ DEC o (3+length F+s1)
           :: INC m 
           :: DEC zero s1 
           :: nil.

    Notation Q2 := min_Q2.

    Local Fact min_Q2_length : length Q2 = 3+length F.
    Proof. unfold Q2; rew length; lia. Qed.

    Local Fact min_Q1_progress e :
                (forall j, zero <= j -> e⇢j = 0)
  -> exists e', (forall j, j < n -> e'⇢(j+1+m) = e⇢(j+p)) 
             /\ e'⇢m = 0 
             /\ (forall j, ~ m <= j <= n+m -> e'⇢j = e⇢j)
             /\ (i,Q1) // (i,e) -+> (length Q1+i,e').
    Proof using H1 H2 H3.
      intros G1.
      destruct (@mm_multi_copy_compute tmp zero n p (1+m))
        with (i := i) (e := e) 
        as (e1 & G4 & G5 & G6); try lia.
      1,2: apply G1; lia.
      destruct (@mm_erase_progress m zero)
        with (i := 9*n+i) (e := e1)
        as (e2 & G9 & G10); try lia.
      1: rewrite G5, G1; lia.
      exists e2; msplit 3.
      * intros; rewrite G9, get_set_env_neq, <- Nat.add_assoc, G4; auto; lia.
      * rewrite G9; rew env.
      * intros; rewrite G9, get_set_env_neq, G5; auto; lia. 
      * rewrite min_Q1_length; unfold Q1.
        apply sss_compute_progress_trans with (9*n+i,e1).
        { revert G6; apply subcode_sss_compute; auto. }
        { replace (2+9*n+i) with (2+(9*n+i)) by lia.
          revert G10; apply subcode_sss_progress; auto. }
    Qed.

    Local Fact min_Q2_0_progress v e : 
                (forall j, zero <= j -> e⇢j = 0)
             -> (forall j, vec_pos v j = e⇢(pos2nat j+1+m))
             -> ⟦f⟧ (e⇢m##v) 0
  -> exists e', (forall j, j <> o -> e'⇢j = e⇢j)
             /\ e'⇢o = 0 
             /\ (s1,Q2) // (s1,e) -+> (length Q2+s1,e').
    Proof.
      intros G1 G2 G3.
      destruct min_HF1 with (1 := G3) (e := e) as (e1 & G4 & G5); auto.
      { intros j; analyse pos j; simpl.
        * rewrite pos2nat_fst; auto.
        * rewrite pos2nat_nxt, G2; f_equal; lia. }
      exists e1; msplit 2.
      1,2: intros; rewrite G4; rew env.
      apply sss_compute_progress_trans with (length F+s1,e1).
      * unfold Q2; revert G5; apply subcode_sss_compute; auto.
      * rewrite min_Q2_length; unfold Q2.
        mm env DEC zero with o (3+length F+s1).
        1: rewrite G4; rew env.
        mm env stop.
    Qed.

    Local Fact min_Q2_S_progress x v e : 
                (forall j, zero <= j -> e⇢j = 0)
             -> (forall j, vec_pos v j = e⇢(pos2nat j+1+m))
             -> ⟦f⟧ (e⇢m##v) (S x)
  -> exists e', (forall j, j <> o -> j <> m -> e'⇢j = e⇢j)
             /\ e'⇢o = x
             /\ e'⇢m = S (e⇢m)
             /\ (s1,Q2) // (s1,e) -+> (s1,e').
    Proof.
      intros G1 G2 G3.
      destruct min_HF1 with (1 := G3) (e := e) as (e1 & G4 & G5); auto.
      { intros j; analyse pos j; simpl.
        * rewrite pos2nat_fst; auto.
        * rewrite pos2nat_nxt, G2; f_equal; lia. }
      exists (e1⦃o⇠x⦄⦃m⇠S (e⇢m)⦄); msplit 3.
      1,3: intros; rew env; rewrite G4; rew env.
      1: clear G5; dest o m; lia.
      apply sss_compute_progress_trans with (length F+s1,e1).
      { unfold Q2; revert G5; apply subcode_sss_compute; auto. }
      unfold Q2.
      mm env DEC S with o (3 + length F + s1) x.
      { rewrite G4; rew env. }
      mm env INC with m.
      mm env DEC zero with zero s1.
      { do 2 (rewrite get_set_env_neq; try lia).
        rewrite G4, get_set_env_neq, G1; lia. }
      mm env stop; f_equal.
      clear G5.
      dest o m; try lia.
      rewrite G4; rew env.
    Qed.

    Local Fact min_Q2_progress_rec v e k :
                (forall j, zero <= j -> e⇢j = 0)
             -> (forall j, vec_pos v j = e⇢(pos2nat j+1+m))
             -> (forall i, i < k -> exists x, ⟦f⟧ (i+(e⇢m)##v) (S x))
  -> exists e', (forall j, j <> o -> j <> m -> e'⇢j = e⇢j)
             /\ e'⇢m = k+(e⇢m)
             /\ (s1,Q2) // (s1,e) ->> (s1,e').
    Proof.
      revert e; induction k as [ | k IHk ]; intros e G1 G2 G3.
      + exists e; msplit 2; auto; mm env stop.
      + destruct (G3 0) as (x & Hx); try lia; simpl in Hx.
        destruct min_Q2_S_progress 
          with (v := v) (e := e) (x := x)
          as (e1 & G4 & _ & G5 & G6); auto.
        destruct IHk with (e := e1)
          as (e2 & G7 & G8 & G9).
        { intros; rewrite G4, G1; lia. }
        { intros j; rewrite G2, G4; auto; lia. }
        { intros j Hj; rewrite G5.
          replace (j+S(e⇢m)) with ((S j)+(e⇢m)) by lia.
          apply G3; lia. }
        exists e2; msplit 2.
        * intros; rewrite G7, G4; auto.
        * rewrite G8, G5; lia.
        * apply sss_compute_trans with (2 := G9).
          apply sss_progress_compute; auto.
    Qed.

    Local Fact min_Q2_compute_rev v e :
              (forall j, zero <= j -> e⇢j = 0)
           -> (forall j, vec_pos v j = e⇢(pos2nat j+1+m))
           -> (s1,Q2) // (s1,e) ↓
           -> exists k, ⟦f⟧ (k+(e⇢m)##v) 0 /\ forall j, j < k -> exists x, ⟦f⟧ (j+(e⇢m)##v) (S x).
    Proof.
      intros G1 G2 ((s2,e') & (q & G3) & G4); simpl fst in G4.
      revert e G1 G2 G3.
      induction on q as IHq with measure q.
      intros e G1 G2 G3.
      destruct min_HF2 with (e := e) (v := (e⇢m)##v)
        as ([ | x ] & Hx); auto.
      { apply subcode_sss_terminates with (Q := (s1,Q2)).
        + unfold Q2; auto.
        + exists (s2,e'); split; auto; exists q; auto. }
      { intros j; analyse pos j.
        + rewrite pos2nat_fst; auto.
        + rewrite pos2nat_nxt; simpl.
          rewrite G2; f_equal; lia. }
      * exists 0; split; auto; intros; lia.
      * destruct min_Q2_S_progress with (v := v) (e := e) (x := x)
          as (e1 & F1 & F2 & F3 & F4); auto.
        destruct subcode_sss_progress_inv with (4 := F4) (5 := G3)
          as (q' & F5 & F6); auto.
        { apply mm_sss_env_fun. }
        { apply subcode_refl. }
        destruct IHq with (4 := F6)
          as (k & Hk1 & Hk2); try lia.
        { intros; rewrite F1, G1; lia. }
        { intros; rewrite G2, F1; auto; lia. }
        exists (S k); split.
        + rewrite F3 in Hk1.
          eq goal Hk1; do 2 f_equal; lia.
        + intros [ | j ] Hj.
          - simpl; exists x; auto.
          - replace (S j + (e⇢m)) with (j+(e1⇢m)).
            apply Hk2; lia.
            rewrite F3; lia.
    Qed.

    Local Fact min_Q2_progress v e k :
                (forall j, zero <= j -> e⇢j = 0)
             -> (forall j, vec_pos v j = e⇢(pos2nat j+1+m))
             -> e⇢m = 0
             -> s_min ⟦f⟧ v k
  -> exists e', (forall j, j <> o -> j <> m -> e'⇢j = e⇢j)
             /\ e'⇢m = k
             /\ (s1,Q2) // (s1,e) -+> (length Q2+s1,e').
    Proof.
      intros G1 G2 G3 (G4 & G5).
      destruct min_Q2_progress_rec with (e := e) (k := k) (v := v)
        as (e1 & G6 & G7 & G8); auto.
      { intros; rewrite G3, Nat.add_comm; auto. }
      destruct min_Q2_0_progress with (v := v) (e := e1)
        as (e2 & G9 & _ & G11).
      { intros; rewrite G6, G1; lia. }
      { intros j; rewrite G2, G6; lia. }
      { rewrite G7, G3, Nat.add_comm; auto. }
      exists e2; msplit 2.
      * intros; rewrite G9, G6; auto.
      * rewrite G9, G7, G3; lia.
      * apply sss_compute_progress_trans with (s1,e1); auto.
    Qed.

    Local Definition min_s4 := length Q1+length Q2+i.

    Notation s4 := min_s4.

    Local Definition min_Q4 := 
              Q1 ++ Q2 
           ++ mm_copy m o tmp zero s4
           ++ mm_multi_erase m zero (1+n) (9+s4).

    Notation Q4 := min_Q4.

    Local Fact min_Q4_progress v e x :
                 (forall j, m <= j -> e⇢j = 0)
              -> (forall j, vec_pos v j = e⇢(pos2nat j+p))
              -> s_min ⟦f⟧ v x
  -> exists e', (forall j, j <> o -> e'⇢j = e⇢j)
              /\ e'⇢o = x
              /\ (i,Q4) // (i,e) -+> (length Q4+i,e').
    Proof.
      intros G1 G2 G3.
      destruct min_Q1_progress with (e := e)
        as (e1 & G4 & G5 & G6 & G7).
      { intros j Hj; apply G1; lia. }
      destruct min_Q2_progress with (v := v) (e := e1) (k := x)
        as (e2 & G8 & G9 & G10); auto.
      { intros j Hj; rewrite G6, G1; lia. }
      { intros j; rewrite G2, G4; auto; apply pos2nat_prop. }
      destruct mm_copy_progress
        with (src := m) (dst := o) (tmp := tmp) (zero := zero)
             (i := s4) (e := e2)
        as (e3 & F1 & F2); try lia.
      1,2: rewrite G8, G6, G1; lia.
      destruct mm_multi_erase_compute 
        with (dst := m) (zero := zero) (k := 1+n)
             (i := 9+s4) (e := e3)
        as (e4 & F3 & F4 & F5); try lia.
      { rewrite F1, get_set_env_neq, G8, G6, G1; lia. }
      exists e4; msplit 2.
      * intros j Hj.
        destruct (interval_dec m zero j).
        + rewrite F3, G1; lia.
        + rewrite F4, F1; rew env; try lia.
          rewrite G8, G6; lia.
      * rewrite F4, F1, G9; rew env; lia.
      * apply sss_progress_trans with (length Q1+i,e1).
        { unfold Q4; revert G7; apply subcode_sss_progress; auto. }
        apply sss_progress_trans with (length Q2+s1,e2).
        { unfold s1 at 1 in G10; revert G10; unfold Q4; apply subcode_sss_progress; auto. }
        apply sss_progress_compute_trans with (9+s4,e3).
        { replace (length Q2+s1) with s4.
          unfold Q4; revert F2; apply subcode_sss_progress; unfold s4; auto.
          unfold s4, s1; lia. }
        { replace (length Q4+i) with (2*(1+n)+(9+s4)).
          unfold Q4; revert F5; apply subcode_sss_compute; auto.
          unfold s4; subcode_tac; rewrite app_nil_r; auto.
          unfold s4, Q4; rew length; lia. }
    Qed.

    Local Fact min_Q4_terminates v e :
                 (forall j, m <= j -> e⇢j = 0)
              -> (forall j, vec_pos v j = e⇢(pos2nat j+p))
              -> (i,Q4) // (i,e) ↓
              -> exists x, s_min ⟦f⟧ v x.
    Proof.
      intros G1 G2 G3.
       destruct min_Q1_progress with (e := e)
        as (e1 & G4 & G5 & G6 & G7).
      { intros j Hj; apply G1; lia. }
      apply subcode_sss_terminates_inv 
        with (P := (i,Q1)) (st1 := (s1,e1)) in G3.
      * apply subcode_sss_terminates with (P := (s1,Q2)) in G3.
        + apply min_Q2_compute_rev with (v := v) in G3.
          - destruct G3 as (x & F1 & F2).
            rewrite G5, Nat.add_comm in F1.
            exists x; split; auto.
            intros j Hj; specialize (F2 _ Hj).
            rewrite G5, Nat.add_comm in F2; auto.
          - intros; rewrite G6, G1; lia.
          - intros; rewrite G2, G4; auto; apply pos2nat_prop.
        + unfold Q4, s1; auto.
      * apply mm_sss_env_fun.
      * unfold Q4; auto.
      * unfold s1; split.
        + apply sss_progress_compute; auto.
        + unfold out_code, code_end, fst, snd; lia.
    Qed.

    Fact ra_compiler_min : ra_compiler_spec (ra_min f) i p o m.
    Proof using Hf H1 H2 H3.
      exists Q4; intros v e G2 G3; split.
      + intros x; simpl ra_rel; intros G1.
        destruct min_Q4_progress with (3 := G1) (e := e)
          as (e' & G4 & G5 & G6); auto.
        exists e'; split.
        * intros j; dest j o.
        * apply sss_progress_compute; auto.
      + intro; apply min_Q4_terminates with (e := e); auto.
    Qed.

  End ra_compiler_min.

  Theorem ra_compiler n f : @ra_compiler_stm n f.
  Proof.
    induction f as [ c | | | n q | n k f g Hf Hg | | ].
    + apply ra_compiler_cst.
    + apply ra_compiler_zero.
    + apply ra_compiler_succ.
    + apply ra_compiler_proj.
    + apply ra_compiler_comp; trivial.
    + intros i p o m ? ? ?; apply ra_compiler_rec; auto.
    + intros i p o m ? ? ?; apply ra_compiler_min; auto.
  Qed. 

  Corollary ra_mm_env_simulator n (f : recalg n) : 
              { P | forall v e,   (forall p, e⇢(pos2nat p) = vec_pos v p)
                               -> (forall j, n < j -> e⇢j = 0)
                               -> (forall x, ⟦f⟧ v x 
                                     -> exists e', e' ⋈ e⦃n⇠x⦄
                                               /\ (1,P) // (1,e) ->> (1+length P,e'))
                               /\ ((1,P) // (1,e) ↓ -> ex (⟦f⟧ v)) }.
  Proof.
    destruct (ra_compiler f) with (i := 1) (p := 0) (o := n) (m := S n)
      as (P & HP); try lia.
    exists P; intros v e H4 H5; split.
    + intros x H3.
      rewrite Nat.add_comm; apply HP with (v := v); auto.
      intros; rewrite Nat.add_comm; simpl; auto.
    + intros H3.
      apply (HP v e); auto.
      intros; rewrite Nat.add_comm; simpl; auto.
  Qed.

End ra_compiler.
