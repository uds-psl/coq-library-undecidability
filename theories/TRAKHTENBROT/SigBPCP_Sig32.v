(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops utils fo_terms fo_logic fo_definable fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section SigBPCP_Sig32_encoding.

  Notation Σ32 := (Σrel_eq 3).

  Let Σ32_var : fo_term nat (ar_syms Σ32) -> nat.
  Proof. intros [ n | [] ]; exact n. Defined.

  Variables (n1 n0 n2 : nat).

  Let ar10 (s : (pos n1 + pos n0)) : nat :=
    match s with inl _ => 1 | inr _ => 0 end.

  Definition Σ10_2 : fo_signature.
  Proof.
    exists (pos n1 + pos n0)%type (pos n2).
    + exact ar10.
    + exact (fun _ => 2).
  Defined.

  Let F1 s t := @in_fot nat _ (ar_syms Σ10_2) (inl s) (t##ø).
  Let C0 s := @in_fot nat _ (ar_syms Σ10_2) (inr s) ø.

  Let E2 x y := fol_atom Σ32 false (£x##£y##ø).
  Let R3 x y z := fol_atom Σ32 true (£x##£y##£z##ø).


  (** maps s1[..sn[v]..] to ([s1;...;sn],inl v) and
           s1[..sn[c]..] to ([s1;...;sn],inr c) *)

  Local Definition term2list : fo_term nat ar10 -> (list (pos n1) * (nat + pos n0))%type.
  Proof.
    induction 1 as [ n | [ s | s ] _ w ] using fo_term_recursion; simpl in *.
    + exact (nil, inl n).
    + apply vec_head in w.
      destruct w as (l,c).
      exact (s::l,c).
    + exact (nil, inr s).
  Defined.

  Local Fact term2list_fix_0 n : term2list (in_var n) = (nil,inl n).
  Proof. apply fo_term_recursion_fix_0. Qed.

  Local Fact term2list_fix_1 s : term2list (in_fot (inr s) ø) = (nil,inr s).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Local Fact term2list_fix_2' s t :
        let (l,c) := term2list t 
        in term2list (in_fot (inl s) (t##ø)) = (s::l,c).
  Proof. 
    unfold term2list at 2; rewrite fo_term_recursion_fix_1; rew vec.
    case_eq (term2list t); intros l c E.
    simpl vec_map; simpl vec_head.
    change ((let (l',c') := term2list t in (s::l',c')) = (s::l,c)).
    rewrite E; auto.
  Qed.

  Local Fact term2list_fix_2 s t :
         term2list (in_fot (inl s) (t##ø)) = (s::fst (term2list t),snd (term2list t)).
  Proof.
    generalize (term2list_fix_2' s t).
    destruct (term2list t); auto.
  Qed.
 
  Opaque term2list.

  Fact term2list_spec t : t = let (l,c) := term2list t in 
                              let t0 := match c with inl n => £n | inr c => in_fot (inr c) ø end
                              in fold_right F1 t0 l.
  Proof.
    induction t as [ n | s v IHv ] using fo_term_pos_rect.
    + rewrite term2list_fix_0; simpl; auto.
    + revert IHv; destruct s as [ s | s ]; simpl in v |- *.
      * vec split v with x; vec nil v; clear v; intros IH.
        specialize (IH pos0); simpl in IH; revert IH.
        generalize (term2list_fix_2 s x).
        destruct (term2list x) as (l,c); simpl; intros -> ->; simpl; auto.
      * intros _; vec nil v; clear v. 
        rewrite term2list_fix_1; simpl; auto.
  Qed.

  Fact term2list_vars t : fo_term_vars t = match snd (term2list t) with inl v => v::nil | _ => nil end.
  Proof.
    induction t as [ n | [] v IHv ] using fo_term_pos_rect; rew fot.
    + rewrite term2list_fix_0; simpl; auto.
    + simpl in v; generalize (IHv pos0); clear IHv.
      vec split v with t; vec nil v; clear v; simpl.
      rewrite term2list_fix_2, <- app_nil_end; simpl; auto.
    + vec nil v; rewrite term2list_fix_1; simpl; auto.
  Qed.

  Let tlift (t : fo_term nat (ar_syms Σ10_2)) n := fo_term_map (plus n) t.

  Fact term2list_lift t n : term2list (tlift t n) = (fst (term2list t), match snd (term2list t) with 
                              | inl v => inl (n+v)
                              | inr c => inr c
                            end).
  Proof.
    induction t as [ v | [] w IHw ] using fo_term_pos_rect; simpl.
    + do 2 rewrite term2list_fix_0; auto.
    + revert IHw; simpl in w; vec split w with t; vec nil w; clear w.
      intros IHw; simpl. 
      do 2 rewrite term2list_fix_2; simpl.
      specialize (IHw pos0); simpl in IHw; rewrite IHw.
      destruct (term2list t) as (l,[]); simpl; auto.
    + clear IHw; simpl in w; vec nil w.
      rewrite term2list_fix_1; auto.
  Qed.

  (** The reduction is based on the following encoding of a model of
      Σ10_2 into a model of Σ32

      Let M be a model of Σ10_2 ie
          f1 : pos n1 -> M -> M
          c0 : pos n0 -> M
          r2 : pos n2 -> M -> M -> Prop

      Let N := unit + pos n1 + pos n2 + M the model of Σ32
      defined by r3 : N -> N -> N -> Prop

        r3 a b c -> a,b ∈ M and c ∈ unit + pos n1 + pos n2
        r3 m1 m2 tt  <->  m1 = m2 ∈ M
        r3 m1 m2 p1  <->  m2 = f1 p1 m1 holds in M
        r3 m1 m2 p2  <->  r2 p2 m1 m2 holds in M

      and the interpreted identity

      For the soundness of the encoding, the simulation relation 
      M <~~> (unit + pos n1 + pos n2) + M would 
      be ⋈ : M -> N -> Prop defined by

             m ⋈ inl _ := False
             m ⋈ inr n := m = n

      For the completeness, we have to extract M from N as
      M := { m | r3 m m tt } and define the simulation relation
      as 

             m ⋈ n := proj1_sig m = n

      The r3 encodes any info. contained in M but also satisfies
      properties like 
        r3 _ _ p1 defines a functional relation

      N is given with a valuation that maps 
        ψ 0 = tt
        ψ (1+p1) = p1
        ψ (1+n1+p0) = p0
        ψ (1+n1+n0+p2) = p2
      
  *)

  Check in_fot.


(*  Let flift (A : fol_form Σ32) := fol_subst (fun n => £ (S n)) A. *)

  Variable (X : Type) (M : fo_model Σ10_2 X)
           (Y : Type) (N : fo_model Σ32 Y).

  Hypothesis (Neq : fom_rels N false = rel2_on_vec eq).  

  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
  Notation "⟪ A ⟫'" := (fun ψ => fol_sem N ψ A) (at level 1, format "⟪ A ⟫'").

  Implicit Types (lu : nat)            (* To encode X into Y as R3 x _ tt  *)
                 (lf : pos n1 -> nat)  (* To encode unary functions        *)
                 (lc : pos n0 -> nat)  (* To encode constants              *)
                 (lr : pos n2 -> nat). (* To encode binary rels            *)

 
  Let f1 s x := fom_syms M (inl s) (x##ø).
  Let c0 s := fom_syms M (inr s) ø.
  Let r2 s x y := fom_rels M s (x##y##ø).

  Let r3 x y z := fom_rels N true (x##y##z##ø).

  Hint Resolve pos_list_prop.

  (** Well formedness of r3 *)

  Definition Σ32_wf1 lu := ∀∀∀ R3 2 1 0 ⤑ R3 2 2 (3+lu).
  Definition Σ32_wf2 lu := ∀∀∀ R3 2 1 0 ⤑ R3 1 1 (3+lu).
  Definition Σ32_wf3 lu lf lr := ∀∀∀ R3 2 1 0 ⤑ fol_ldisj (map (fun n => E2 0 (3+n)) (lu::map lf (pos_list _)++map lr (pos_list _))).

  Fact Σ32_wf1_spec lu ψ : ⟪Σ32_wf1 lu⟫' ψ = forall a b c, r3 a b c -> r3 a a (ψ lu).
  Proof. reflexivity. Qed.

  Fact Σ32_wf2_spec lu ψ : ⟪Σ32_wf2 lu⟫' ψ = forall a b c, r3 a b c -> r3 b b (ψ lu).
  Proof. reflexivity. Qed.

  Fact Σ32_wf3_spec lu lf lr ψ : 
          ⟪Σ32_wf3 lu lf lr⟫' ψ 
      <-> forall a b c, r3 a b c -> c = ψ lu \/ (exists s, c = ψ (lf s)) \/ (exists s, c = ψ (lr s)).
  Proof.
    unfold Σ32_wf3; simpl.
    do 3 (apply forall_equiv; intro).
    apply fol_bin_sem_ext with (b := fol_imp); try tauto.
    apply fol_bin_sem_ext with (b := fol_disj).
    + rewrite Neq; simpl; tauto.
    + rewrite map_app, map_map, map_map, fol_sem_ldisj_app.
      apply fol_bin_sem_ext with (b := fol_disj); rewrite fol_sem_ldisj; split.
      * intros (f & H1 & H2); revert H1 H2; rewrite in_map_iff.
        intros (s & <- & H1) H3; simpl in *; exists s.
        revert H3; rewrite Neq; auto.
      * intros (s & ->).
        exists (E2 0 (3+lf s)); split; simpl.
        ++ apply in_map_iff; exists s; split; auto.
        ++ rewrite Neq; simpl; auto.
      * intros (f & H1 & H2); revert H1 H2; rewrite in_map_iff.
        intros (s & <- & H1) H3; simpl in *; exists s.
        revert H3; rewrite Neq; auto.
      * intros (s & ->).
        exists (E2 0 (3+lr s)); split; simpl.
        ++ apply in_map_iff; exists s; split; auto.
        ++ rewrite Neq; simpl; auto.
  Qed.

  (** r3 _ _ (ψ (lf s)) describes total function graphs *)

  Definition Σ32_fun lf (s : pos n1) : fol_form Σ32 :=
       ∀∀∀ R3 1 2 (3+lf s) ⤑ R3 0 2 (3+lf s) ⤑ E2 1 0.

  Fact Σ32_fun_spec lf ψ s : ⟪Σ32_fun lf s⟫' ψ <-> graph_fun (fun x y => r3 y x (ψ (lf s))).
  Proof.
    unfold Σ32_fun, graph_fun; simpl.
    do 3 (apply forall_equiv; intro).
    change (x0=x1) with (rel2_on_vec eq (x0##x1##ø)); rewrite <- Neq.
    apply fol_equiv_ext; auto.
  Qed.

  Definition Σ32_tot lu lf s : fol_form Σ32 := ∀ R3 0 0 (1+lu) ⤑ ∃ R3 0 1 (2+lf s) ⟑ R3 0 0 (2+lu).

  Fact Σ32_tot_spec lu lf ψ s : ⟪Σ32_tot lu lf s⟫' ψ = forall x, r3 x x (ψ lu) -> exists y, r3 y x (ψ (lf s))
                                                                                         /\ r3 y y (ψ lu).
  Proof. reflexivity. Qed.

  Definition Σ32_functions lu lf := fol_lconj (map (fun s => Σ32_fun lf s ⟑ Σ32_tot lu lf s) (pos_list n1)).

  Fact Σ32_functions_spec lu lf ψ : ⟪Σ32_functions lu lf⟫' ψ 
                                <-> forall s, graph_fun (fun x y => r3 y x (ψ (lf s)))
                                           /\ forall x, r3 x x (ψ lu) -> exists y, r3 y x (ψ (lf s)) /\ r3 y y (ψ lu).
  Proof.
    Opaque Σ32_fun Σ32_tot.
    unfold Σ32_functions.
    rewrite fol_sem_lconj; split.
    + intros H s.
      rewrite <- Σ32_fun_spec, <- Σ32_tot_spec.
      apply (H (Σ32_fun lf s ⟑ Σ32_tot lu lf s)), in_map_iff.
      exists s; auto.
    + intros H f; rewrite in_map_iff.
      intros (s & <- & Hs); simpl.
      rewrite Σ32_fun_spec, Σ32_tot_spec.
      apply H.
  Qed.

  Section Σ32_chain.

    Variable lf : pos n1 -> nat.
    Variable lc : pos n0 -> nat.
    Variable t : fo_term nat ar10.
    Variable y : nat.

    Let l := fst (term2list t).
    Let c := snd (term2list t).
    Let x := match c with inl n => n | inr s => lc s end.

    Let chain : @fol_definable Σ32 nil (true::false::nil) _ N
                             (fun ψ => rel_chain (fun z x y => r3 x y z) (ψ y) (map (fun s => ψ (lf s)) l) (ψ x)).
    Proof.
      apply fol_def_rel_chain'; fol def.
      + apply fol_def_equiv with (R := fun φ => fom_rels N false (φ 0##φ 1##ø)).
        * intros; rewrite Neq; simpl; tauto.
        * apply fol_def_atom with (r := false); auto.
          - simpl; auto.
          - intros p; simpl in p. 
            repeat (invert pos p; fol def).
      + apply fol_def_atom with (r := true).
        * simpl; auto.
        * intros p; simpl in p.
          repeat (invert pos p; fol def).
    Qed.

    Definition Σ32_chain := proj1_sig chain.

    Fact Σ32_chain_spec ψ : ⟪Σ32_chain⟫' ψ <-> rel_chain (fun z x y => r3 x y z) (ψ y) (map (fun s => ψ (lf s)) l) (ψ x).
    Proof. apply (proj2_sig chain). Qed.

  End Σ32_chain.

  Check Σ32_chain_spec.

  Let llift K (f : K -> nat) n k := n+(f k). 

  Fixpoint Σ10_2_to_Σ32 lu lf lc lr (A : fol_form Σ10_2) : fol_form Σ32 :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ r v => ∃ ∃ R3 0 1 (2+lr r) 
                            ⟑ Σ32_chain (llift lf 2) (llift lc 2) (tlift (vec_head v) 2) 0
                            ⟑ Σ32_chain (llift lf 2) (llift lc 2) (tlift (vec_head (vec_tail v)) 2) 1
      | fol_bin b A B  => fol_bin b (Σ10_2_to_Σ32 lu lf lc lr A) (Σ10_2_to_Σ32 lu lf lc lr B)
      | ∀ A => ∀ R3 0 0 lu ⤑ (Σ10_2_to_Σ32 (S lu) (llift lf 1) (llift lc 1) (llift lr 1) A)
      | ∃ A => ∃ R3 0 0 lu ⟑ (Σ10_2_to_Σ32 (S lu) (llift lf 1) (llift lc 1) (llift lr 1) A)
    end.

  Variable (simul : X -> Y -> Prop).

  Hypothesis Hsimul_fun : graph_fun simul.

  Infix "⋈" := simul (at level 70, no associativity).

  Local Definition Hsim_dec := forall x y, { x ⋈ y } + { ~ x ⋈ y }.
  Local Definition Hsim_fin := finite_t X.
  Local Definition HN_dec := fo_model_dec N.

  Local Fact HN_dec_r3 : HN_dec -> forall a b c, { r3 a b c } + { ~ r3 a b c }.
  Proof. intros H ? ? ?; apply (H true (_##_##_##ø)). Qed.

  Local Fact HN_dec_eq : HN_dec -> forall a b : Y, { a = b } + { a <> b }.
  Proof.
    intros H a b; generalize (H false (a##b##ø)). 
    intros [ H1 | H1 ]; revert H1; rewrite Neq; simpl; auto.
  Qed.

  Local Fact fot_sem_F1 l t φ : fo_term_sem (fom_syms M) φ (fold_right F1 t l) = fold_right f1 (fo_term_sem (fom_syms M) φ t) l.
  Proof. unfold F1, f1; induction l; simpl; repeat f_equal; auto. Qed.

  Local Fact rel_chains_1 lf l t y φ ψ :
                (forall s x y, x ⋈ y -> exists sy, f1 s x ⋈ sy /\ r3 sy y (ψ (lf s)))
             -> fo_term_sem (fom_syms M) φ t ⋈ y 
             -> exists sy, fo_term_sem (fom_syms M) φ (fold_right F1 t l) ⋈ sy 
                        /\ rel_chain (fun s x y => r3 x y (ψ (lf s))) sy l y.
  Proof.
    intros H3 H2.
    apply rel_chain_simul_tot with (R := fun s y x => y = f1 s x) (2 := H2).
    + intros; subst; auto.
    + rewrite rel_chain_fold with (f := f1); try tauto.
      apply fot_sem_F1.
  Qed.
 
  Theorem Σ10_2_to_Σ32_correct lu lf lc lr A φ ψ:
           (forall x, exists y, x ⋈ y /\ r3 y y (ψ lu))
        -> (forall s x y, x ⋈ y -> exists sy, f1 s x ⋈ sy /\ r3 sy y (ψ (lf s)))
        -> (forall s y, c0 s ⋈ y <-> y = ψ (lc s))
        -> (forall s x1 x2 y1 y2, x1 ⋈ y1 -> x2 ⋈ y2 -> r2 s x1 x2 <-> r3 y1 y2 (ψ (lr s))) 
        -> (forall x, In x (fol_vars A) -> φ x ⋈ ψ x)
        -> ⟪ A ⟫ φ <-> ⟪Σ10_2_to_Σ32 lu lf lc lr A⟫' ψ.
  Proof.
    revert lu lf lc lr φ ψ.
    induction A as [ | r v | b A HA B HB | q A HA ]; intros lu lf lc lr phi psi H1 H2 H3 H4 H5; simpl; try tauto.
    + split.
      * revert v H5; simpl; intros v.
        vec split v with t1; vec split v with t2; vec nil v; clear v.
        simpl; intros H5 Hr.
        destruct (H1 (fo_term_sem (fom_syms M) phi t1)) as (y1 & G1 & G2).
        destruct (H1 (fo_term_sem (fom_syms M) phi t2)) as (y2 & G3 & G4).
        exists y2, y1; msplit 2.
        - change (r3 y1 y2 (psi (lr r))).
          rewrite <- (H4 r) with (1 := G1) (2 := G3); auto.
        - rewrite Σ32_chain_spec; simpl.
          rewrite rel_chain_map.
          rewrite term2list_lift.
          generalize (term2list_vars t1) (term2list_spec t1).
          destruct (term2list t1) as (l,[n|s]); intros E1 E0.
          ++ assert (phi n ⋈ psi n) by (apply H5; rewrite E1; simpl; auto); clear E1.
             destruct (rel_chains_1) with (1 := H2) (l := l) (t := @in_var _ _ (ar_syms Σ10_2)  n)
               (φ := phi) (y := psi n) as (sy & G5 & G6); rew fot; auto; simpl.
             simpl in E0; rewrite E0 in G1.
             rewrite (Hsimul_fun G1 G5); auto.
          ++ simpl. 
             destruct (rel_chains_1) with (1 := H2) (l := l) (t := C0 s)
               (φ := phi) (y := psi (lc s)) as (sy & G5 & G6); rew fot; auto; simpl.
             ** apply H3; auto.
             ** simpl in E0; rewrite E0 in G1.
                rewrite (Hsimul_fun G1 G5); auto.
        - rewrite Σ32_chain_spec; simpl.
          rewrite rel_chain_map.
          rewrite term2list_lift.
          generalize (term2list_vars t2) (term2list_spec t2).
          destruct (term2list t2) as (l,[n|s]); intros E1 E0.
          ++ simpl; assert (phi n ⋈ psi n).
             { apply H5; rewrite E1; simpl; apply in_or_app; simpl; auto. } 
             clear E1.
             destruct (rel_chains_1) with (1 := H2) (l := l) (t := @in_var _ _ (ar_syms Σ10_2)  n)
               (φ := phi) (y := psi n) as (sy & G5 & G6); rew fot; auto; simpl.
             simpl in E0; rewrite E0 in G3.
             rewrite (Hsimul_fun G3 G5); auto.
          ++ simpl. 
             destruct (rel_chains_1) with (1 := H2) (l := l) (t := C0 s)
               (φ := phi) (y := psi (lc s)) as (sy & G5 & G6); rew fot; auto; simpl.
             ** apply H3; auto.
             ** simpl in E0; rewrite E0 in G3.
                rewrite (Hsimul_fun G3 G5); auto.
      * revert v H5; intros v; simpl in v.
        vec split v with t1; vec split v with t2; vec nil v; clear v.
        intros H5 (y2 & y1 & G1 & G2 & G3).
        change (r3 y1 y2 (psi (lr r))) in G1.
        rewrite Σ32_chain_spec, rel_chain_map, term2list_lift in G2.
        rewrite Σ32_chain_spec, rel_chain_map, term2list_lift in G3.
        simpl in G2, G3.
        generalize (term2list_vars t1) (term2list_spec t1).
        destruct (term2list t1) as (l1,c1); intros K1 K2.
        generalize (term2list_vars t2) (term2list_spec t2).
        destruct (term2list t2) as (l2,c2); intros K3 K4.
        simpl in G2, G3.
        simpl in K2, K4.
        rewrite K2, K4; simpl.
        apply H4 with y1 y2; auto.
        - rewrite  fot_sem_F1.
          admit.
        - admit.
    + apply fol_bin_sem_ext.
      * apply HA; auto; intros; apply H5, in_or_app; auto.
      * apply HB; auto; intros; apply H5, in_or_app; auto.
    + admit.

  Admitted. 

End SigBPCP_Sig32_encoding.

Check Σ10_2_to_Σ32.


  Section functions.

    Variables (lu : nat) (lf : pos n1 -> nat) (lc : pos n0 -> nat) (lr : pos n2 -> nat) (ψ : nat -> Y). 

    Let Hsim_eq1 := forall x, { y | r3 y y (ψ lu) /\ x ⋈ y }.
    Let Hsim_eq2 := forall y, r3 y y (ψ lu) -> { x | x ⋈ y }.
    Let Hsim_eq3 := graph_fun simul.
    Let Hsim_eq4 := graph_fun (fun y x => x ⋈ y).
    Local Definition Hsim_eq := (Hsim_eq1 * Hsim_eq2 * (Hsim_eq3 * Hsim_eq4))%type.

    Local Definition Hsim_wf := ⟪Σ32_wf1 lu ⟑ Σ32_wf2 lu ⟑ Σ32_wf3 lu lf lr⟫' ψ.
    Local Definition Hsim_functions := ⟪Σ32_functions lu lf⟫' ψ.

    Hypothesis (Hfin : Hsim_fin) (HNd : HN_dec) (He : Hsim_eq) (Hf : Hsim_functions).

    Let extract s : { f | forall x y sy, x ⋈ y -> f x ⋈ sy -> r3 sy y (ψ (lf s)) }.
    Proof.
      set (R (x1 x2 : X) := exists y sy, x1 ⋈ y /\ x2 ⋈ sy /\ r3 sy y (ψ (lf s))).
      destruct He as ((H1 & H2) & (F1 & F2)).
      red in Hf.
      rewrite Σ32_functions_spec in Hf.
      specialize (Hf s).
      destruct Hf as (H3 & H4).
      destruct graph_tot_reif with (R := R) as (h & Hh); auto.
      + intros x1 x2.
        destruct (H1 x1) as (y & Hy1 & Hy2).
        destruct (H1 x2) as (sy & Hs1 & Hs2).
        destruct (HN_dec_r3 HNd sy y (ψ (lf s))) as [ H | H ]; [ left | right ].
        * exists y, sy; auto.
        * contradict H; revert H; intros (y' & sy' & G1 & G2 & G3).
          rewrite (F1 _ _ _ Hy2 G1), (F1 _ _ _ Hs2 G2); auto.
      + split. 
        * intros x x1 x2 (y1 & s1 & G1 & G2 & G3) (y2 & s2 & G4 & G5 & G6).
          generalize (F1 _ _ _ G1 G4); intros; subst y2.
          generalize (H3 _ _ _ G3 G6); intros; subst s2.
          apply (F2 _ _ _ G2 G5).
        * intros x.
          destruct (H1 x) as (y & G1 & G2).
          destruct (H4 _ G1) as (sy & G3 & G4).
          destruct (H2 _ G4) as (fx & Hfx).
          exists fx, y, sy; auto.
      + exists h; intros x y sy G1 G2.
        specialize (proj2 (Hh x _) eq_refl).
        intros (y' & sy' & G3 & G4 & G5).
        rewrite (F1 _ _ _ G1 G3), (F1 _ _ _ G2 G4); auto.
    Qed.

    Local Fact Hsim_functions_extract : 
           { f : pos n1 -> X -> X | forall s x y sy, x ⋈ y -> f s x ⋈ sy -> r3 sy y (ψ (lf s)) }.
    Proof. apply pos_reif_t in extract; auto. Qed.

  End functions.

  (** We have rebuild the functions encoded in r3 *)

  Check Hsim_functions_extract.

  (** I should better review the hypotheses here perhaps to make that more specific
      toward the particular models this encoding is aimed at *)
  
  Definition Hsim1 lu ψ := forall x, exists y, r3 y y (ψ lu) /\ simul x y.
  Definition Hsim2 lu ψ := forall y, r3 y y (ψ lu) -> exists x, simul x y.
  Definition Hsim3 lu lf ψ := forall s y, r3 y y (ψ lu) -> r3 (f1' s y) y (ψ (lf s)).
  Definition Hsim4 lu lc ψ := forall s, r3 (c0' s) (c0' s) (ψ lu).

  Definition Hsim5 lf ψ := forall s x y, simul x y -> exists sy, r3 sy y (ψ (lf s)) /\ simul (f1 s x) sy.
  Definition Hsim6 lc ψ := forall s, exists y, r3 y y (ψ (lc s)) /\ simul (c0 s) y.
  Definition Hsim7 lr ψ := forall r x x' y y', simul x y -> simul x' y' -> r2 r x x' <-> r3 y y' (ψ (lr r)).

  Definition Hsim8 lf ψ := forall s x x' y y', simul x y -> simul x' y' -> x' = f1 s x <-> r3 y' y (ψ (lf s)). 

  Fact  Σ32_chain_spec' lf lc t y φ ψ : 
            Hsim8 lf ψ
         -> (forall n, In n (fo_term_vars t) -> simul (φ n) (ψ n))
         -> ⟪Σ32_chain lf lc t y⟫' ψ <-> φ y = fo_term_sem (fom_syms M) φ t.
  Proof.
    intros H1 H2.
    rewrite Σ32_chain_spec.
    rewrite rel3_chain_spec with (f := f1').
    + generalize (term2list_spec t); destruct (term2list t) as (l,c); intros ->.
      red in H1; simpl.
      revert y; induction l as [ | s l IHl ]; intros y; simpl.
      * destruct c; rew fot; simpl.
        - admit.
        - admit.
      * unfold f1 in H1; rewrite H1.
       
      
    

  Theorem Hsimul lu lf lc lr A φ ψ : 
            Hsim1 lu ψ
         -> Hsim2 lu ψ
         -> Hsim3 lf ψ
         -> Hsim4 lc ψ
         -> Hsim5 lr ψ
         -> Hsim6 lf ψ
         -> (forall n, In n (fol_vars A) -> simul (φ n) (ψ n))
         -> ⟪A⟫ φ <-> ⟪Σ10_2_to_Σ32 lu lf lc lr A⟫' ψ.
  Proof.
    revert lu lf lc lr φ ψ.
    induction A as [ 
 
  Section coding_a_term.

    (** Find formula A such that ⟪A t y⟫ <-> rel3_chain R3 y l c 
        where (l,c) := term2list t 

        Use the fact that rel3_chain is fol_definable
     *)

  End coding_a_term.

  (* ψ maps 0 ... (f1+c0+r2) to tt + pos f1 + pos c0 + pos r2 *)
 
  Check rel3_chain_spec.

  Let f  

  Fact enc_term_sem (t : fo_term nat ar10) f g x phi psi :
               let a := fo_term_sem (fom_syms M) phi t 
               in  phi x = a -> fol_sem N psi (enc_term t f g x).

  Variables (i : X -> Y) (j : Y -> X).



