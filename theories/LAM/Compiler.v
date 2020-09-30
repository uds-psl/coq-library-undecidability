From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Tactics.GenEncode L.Util.L_facts.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools LM_heap_def WriteValue Copy.
From Undecidability.LAM Require Import TM.Alphabets TM.StepTM TM.HaltingProblem.
From Undecidability Require Import TM.TM L.AbstractMachines.FlatPro.LM_heap_correct.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.

Definition encTM {Σ : Type} (s b : Σ) (l : list bool) := @midtape Σ [] b (fold_right (fun (x : bool) r => (if x then s else b) :: r) nil l).

Import VectorNotations.

Definition TM_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (k + 1 + n),
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t
                                /\ nth_error (Vector.to_list t) k = Some (encTM s b m)) /\
  (forall q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t ->
          exists m, nth_error (Vector.to_list t) k = Some (encTM s b m)).


Definition TM_computable_rel {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : pTM Σ unit (k + 1 + n),
    Realise M (fun t '(_, t') =>
                                       forall v, t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n ->
                                            exists m, nth_error (Vector.to_list t') k = Some (encTM s b m) /\ R v m) /\
    exists f,
      TerminatesIn (projT1 M) (fun t i => exists v m, R v m /\ t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n /\ i >= f k v).

Require Import Equations.Prop.DepElim.

Lemma nth_error_to_list {X n} (v : Vector.t X n) i k :
  k = (proj1_sig (Fin.to_nat i)) ->
  nth_error (Vector.to_list v) k = Some (Vector.nth v i).
Proof.
  intros ->. induction v; cbn.
  - inversion i.
  - dependent destruct i; cbn.
    + reflexivity.
    + destruct (Fin.to_nat p) as (i, P) eqn:E. cbn.
      fold (to_list v).
      specialize (IHv (Fin.of_nat_lt P)). cbn in *.
      rewrite Fin.to_nat_of_nat in IHv. cbn in IHv.
      now rewrite <- (Fin.of_nat_to_nat_inv p), E. 
Qed.

Lemma encTM_inj {Σ} (sym_s sym_b : Σ) n1 n2 :
  sym_s <> sym_b -> encTM sym_s sym_b n1 = encTM sym_s sym_b n2 -> n1 = n2.
Proof.
  intros Hdiff.
  induction n1 in n2 |- *.
  - destruct n2; now inversion 1.
  - destruct n2; inversion 1.
    destruct a, b.
    + f_equal. eapply IHn1. unfold encTM. congruence.
    + now exfalso.
    + now exfalso.
    + f_equal. eapply IHn1. unfold encTM. congruence.
Qed.

Lemma TM_computable_rel_spec k R :
  functional R ->
  @TM_computable_rel k R -> @TM_computable k R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & [M lab] & H1 & f & H2).
  exists n, Σ, s, b. split. exact Hdiff. exists M.
  intros v. split.
  - intros m. split.
    + intros HR.
      destruct (H2 ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) (f k v)) as [[q' t'] Hconf].
      * exists v, m. split. eauto. split. reflexivity. lia.
      * exists q', t'. split. eapply TM_eval_iff. eexists. eapply Hconf.
        eapply H1 in Hconf as (m' & Hm1 & Hm2). reflexivity.
        now pose proof (Hfun _ _ _ HR Hm2) as ->.
    + intros (q' & t' & [steps Hter] % TM_eval_iff & Hout).
      eapply H1 in Hter as (m' & Hm1 & Hm2). reflexivity.
      cbn -[to_list] in *. 
      rewrite Hm1 in Hout.
      enough (m = m') by now subst.
      eapply encTM_inj; eauto. congruence.
  - intros q t [steps Hter] % TM_eval_iff.
    eapply H1 in Hter as (m & Hm1 & Hm2). reflexivity.
    exists m. eassumption.
Qed.

Definition TM_computable_rel' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : pTM Σ unit (1 + n + k),
    Realise M (fun t '(_, t') =>
                                       forall v, t = ([niltape] ++ Vector.const niltape n ++ (Vector.map (encTM s b) v)) ->
                                            exists m, Vector.hd t' = encTM s b m /\ R v m) /\
    exists f,
      TerminatesIn (projT1 M) (fun t i => exists v m, R v m /\ t = ([niltape] ++ Vector.const niltape n ++ (Vector.map (encTM s b) v)) /\ i >= f k v).

Lemma Vector_nth_L {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.L k2 i] = v1[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - dependent destruct i.
  - dependent destruct i.
    + reflexivity.
    + cbn. eapply IHv1.
Qed.

Lemma Vector_nth_R {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.R k1 i] = v2[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - reflexivity.
  - cbn. eapply IHv1.
Qed.

Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) :
  Vector.map f (v1 ++ v2) = Vector.map f v1 ++ Vector.map f v2.
Proof.
  induction v1; cbn; congruence.
Qed.

Lemma TM_computable_rel'_spec k R :
  functional R ->
  @TM_computable_rel' k R -> TM_computable R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & M & H1 & f & H2).
  eapply TM_computable_rel_spec. eassumption.
  exists n, Σ, s, b. split. exact Hdiff.
  eexists (LiftTapes M (Fin.L n (Fin.R k Fin0) :::  tabulate (n := n) (fun x => Fin.R (k + 1) x) ++ (tabulate (n := k) (fun x => Fin.L n (Fin.L 1 x))))).
  split.
  - eapply Realise_monotone. eapply LiftTapes_Realise. admit. eapply H1.
    intros tps [[] tps'] H v ->.
    cbn in H. destruct H as [H H'].
    destruct (H v) as (m & Hm1 & Hm2).
    + f_equal.
      * rewrite Vector_nth_L, Vector_nth_R. reflexivity.
      * admit.
    + exists m. split. 2:eassumption. erewrite nth_error_to_list, Hm1. reflexivity.
      rewrite Fin.L_sanity, Fin.R_sanity. cbn. lia.
  - exists f. eapply TerminatesIn_monotone.
    eapply LiftTapes_Terminates. admit. eapply H2.
    intros tps i (v & m & HR & -> & Hf); subst.
    exists v, m. split. eauto. split; try eassumption.
    { unfold select. clear. cbn. f_equal.
      now rewrite Vector_nth_L, Vector_nth_R.
      rewrite Vector_map_app. f_equal.
      - admit.
      - admit.
    }
Admitted.

Definition encL (l : list bool) := list_enc l.

Definition L_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) o -> exists m, o = encL m).

Fixpoint encL' (l : list bool) :=
  match l with
  | nil => enc (@List.nil bool)
  | b :: l => L.app (L.app (ext (@List.cons bool)) (ext b)) (encL' l)
  end%list.

Definition L_computable' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL' n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL' n)) s v) o -> exists m, o = encL m).

Lemma encL_encL' l :
  encL' l >* encL l.
Proof.
  induction l.
  - reflexivity.
  - cbn. Lsimpl.
Admitted.

Lemma encL_encL'_fold_eval s t {k} (v : Vector.t (list bool) k) res :
  s >* t ->
  L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL' n)) s v) res <->
  L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) t v) res.
Proof.
  intros Hst.
  induction v as [ | l k v IH] in s, t, Hst |- *; cbn.
  - rewrite !eval_iff. split; intros []; split; eauto.
    + eapply equiv_lambda. eauto. now rewrite <- Hst, H.
    + now rewrite Hst.
  - rewrite IH. reflexivity.
    now rewrite encL_encL', Hst.
Qed.

Lemma L_computable'_spec k R :
  @L_computable k R -> L_computable' R.
Proof.
  intros [s H]. exists s. intros v.
  specialize (H v) as [H1 H2].
  split.
  - intros res. now rewrite H1, encL_encL'_fold_eval.
  - intros res H. eapply encL_encL'_fold_eval in H. 2:reflexivity.
    now eapply H2 in H.
Qed.

Import VectorNotations.

Section APP_right.

  Definition APP_right : pTM (sigPro)^+ unit 2.
  Admitted.

  Lemma APP_right_realise :
    Realise APP_right (fun t '(r, t') => forall s1 s2 : L.term, t[@Fin0] ≃ compile s1 -> t[@Fin1] ≃ compile s2 -> t'[@Fin0] ≃ compile (L.app s1 s2)).
  Admitted.

End APP_right.

Section mk_init_one.

  Variable Σ : finType.

  Variable s b : Σ^+.
  Context {H : codable Σ (list Tok)}.

  Definition M_init_one : pTM (Σ) ^+ unit 3. Admitted.

  Lemma M_init_one_realise :
    Realise M_init_one (fun t '(r, t') =>
                          forall n,
                            t[@Fin0] = encTM s b n ->
                            (* isRight (t[@Fin1]) -> *)
                            (* isRight (t[@Fin2]) -> *)
                          forall ter : L.term,
                            t[@Fin1] ≃ compile ter ->
                            t'[@Fin1] ≃ compile (L.app ter (encL' n))
                       ).
  Admitted.

End  mk_init_one.

Section mk_init.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Context {Henc1 : codable Σ (list Tok)}.
  Context {Henc2 : codable Σ (list (nat * list Tok))}.

  Variable n : nat.

  Variable output1 : Fin.t n.
  Variable output2 : Fin.t n.
  Variable output3 : Fin.t n.
  Variable help1 : Fin.t n.
  Variable help2 : Fin.t n.

  Variable sim : term.

  Definition M_init k : pTM (Σ) ^+ unit (n + k). 
  Proof.
  (*   induction k as [ | k_ M_init]. *)
  (*   - exact (LiftTapes (WriteValue (encode (compile sim))) [| Fin.R ( k + 1) (help1) |]). *)
  (*   - refine ( *)
  (*         LiftTapes (M_init_one s b) [| Fin0 ; Fin.R (S k_ + 3) Fin0 ; Fin.R (S k_ + 3) Fin1 |] ;; *)
  (*         LiftTapes M_init (tabulate Fin.FS) *)
  (*       ). *)
  (* Defined. *)
  Admitted.

  Theorem M_init_rel k :
    Realise (M_init k) (fun t '(r, t') =>
                 forall v, 
                   t = Vector.const niltape n ++ Vector.map (encTM s b) v ->
                   t'[@Fin.L k output1] ≃ [(0, compile (Vector.fold_left (fun s l_i => L.app s (encL l_i)) sim v))]%list /\
                   t'[@Fin.L k output2] ≃ []%list /\
                   t'[@Fin.L k output3] ≃ []%list
                   ).
  Proof.
    induction k.
    - (* cbn. eapply Realise_monotone. TM_Correct. *)
      (* intros t [[] t'] [H1 H2] v ->. *)
      (* destruct_tapes. cbn in *. *)
      (* admit. *)
  Admitted.

End mk_init.

Section unfold.

  Variable Σ : finType.
  Context {Henc1 : codable Σ Heap}.
  Context {Henc2 : codable Σ (list HClos)}.
  Context {Henc3 : codable Σ term}.

  Variable n : nat.

  Variable i_g : Fin.t n.
  Variable i_H : Fin.t n.
  Variable o_t : Fin.t n.
    
  Definition M_unf : pTM (Σ) ^+ unit n. Admitted.

  Theorem M_unf_realise :
    Realise M_unf (fun t '(r, t') =>
                     forall g, forall H : Heap, 
                         t[@i_g] ≃ [g]%list ->
                         t[@i_H] ≃ H ->
                         exists t,
                           reprC H g t /\
                           t'[@o_t] ≃ t).
  Admitted.

End unfold.

Section conv_output.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Context {Henc1 : codable Σ Heap}.
  Context {Henc2 : codable Σ (list HClos)}.
  Context {Henc3 : codable Σ (list Tok)}.
    
  Variable n : nat.

  Variable i_l : Fin.t n.
  Variable o_m : Fin.t n.

  Definition M_out : pTM (Σ) ^+ unit n. Admitted.

  Theorem M_out_realise :
    Realise M_out (fun t '(r, t') =>
                     forall l : list bool, t[@i_l] ≃ compile (list_enc l) ->
                                   t'[@o_m] = encTM s b l).
  Admitted.

End conv_output.

Section MK_isRight.

  Variable n : nat.
  Context {Σ : finType}.
  Variable s : Σ.
  Variable i : Fin.t n.

  Definition MK_isRight : pTM Σ unit n.
  Admitted.

  Lemma MK_isRight_realise :
    Realise MK_isRight (fun t '(r, t') => isRight (t'[@i]) /\ forall j, not_index [| i |] j -> t'[@j] = t[@j]).
  Admitted.

End MK_isRight.

Section main.

  Variable k : nat.
  Variable (R : Vector.t (list bool) k -> (list bool) -> Prop).

  Variable s : term.

  Variable Hs1 : (forall v, forall m : list bool,
   R v m <->
   L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL' n)) s v) (encL m)).

  Variable Hs2 : (forall v, forall o : term,
                     L.eval (Vector.fold_left (n := k) (fun (s0 : term) (n : list bool) => L.app s0 (encL' n)) s v) o ->
                     exists m : list bool, o = encL m).

  Axiom todo : forall {A : Type}, A.

  Definition n_main := 18.

  Definition Σ : finType := (sigStep + bool) ^+.

  Definition sym_s : Σ := inr (inr true).
  Definition sym_b : Σ := inr (inr false).

  (*
    auxiliary tapes:

    0    : T
    1    : V
    2    : H
    3-4  : aux for init
    5-12 : aux for loop
    13   : t
   *)

  Notation aux n := (Fin.L k (Fin.R 1 n)).

  Definition garb : Σ := inl UNKNOWN.

  Definition M_main : pTM Σ unit (1 + n_main + k).
  Proof.
    refine (
        M_init sym_s sym_b Fin1 Fin2 Fin3 Fin4 Fin5 s k ;;
        MK_isRight garb ( aux Fin5 ) ;;
        MK_isRight garb ( aux Fin6 ) ;;
        MK_isRight garb ( aux Fin7 ) ;;
        MK_isRight garb ( aux Fin8 ) ;;
        MK_isRight garb ( aux Fin9 ) ;;
        MK_isRight garb ( aux Fin10) ;;
        MK_isRight garb ( aux Fin11) ;;
        MK_isRight garb ( aux Fin12) ;;
        LiftAlphabet (LiftTapes Loop [| aux Fin0 ; aux Fin1 ; aux Fin2 ; aux Fin5 ; aux Fin6 ; aux Fin7 ; aux Fin8 ; aux Fin9 ; aux Fin10 ; aux Fin11 ; aux Fin12 |]) _ (inl UNKNOWN)  ;;
        M_unf (aux Fin1) (aux Fin2) (aux Fin13) ;;
        M_out sym_s sym_b (aux Fin13) Fin0
      ).
    all: exact todo.
  Defined.

  Lemma syms_diff : sym_s <> sym_b. Proof. cbv. congruence. Qed.

  Lemma M_main_realise :
    Realise M_main (fun t '(r, t') =>
                      forall v,
                      t = const niltape (S n_main) ++ Vector.map (encTM sym_s sym_b) v  ->
                      exists m, 
                        t'[@ Fin0] = encTM sym_s sym_b m /\ R v m).
  Proof.
    eapply Realise_monotone.
    {
      eapply Seq_Realise. eapply M_init_rel.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply MK_isRight_realise.
      eapply Seq_Realise. eapply LiftAlphabet_Realise. eapply LiftTapes_Realise. admit. eapply Loop_Realise.
      eapply Seq_Realise. eapply M_unf_realise.
      eapply M_out_realise.
    }
    (* intros tin ([] & tout) H v ->. *)
    (* unfold n_main in *. cbn in tout. *)
    (* destruct_tapes. TMSimp. *)
    (* specialize (H v eq_refl) as [? []]. *)
    (* rewrite <- H2, <- H4, <- H6, <- H8, <- H10, <- H12, <- H14, <- H16 in H, H20, H21. *)
    (* all: try now inversion 1. *)
    (* modpon H15. simpl_surject. *)
    (* TMSimp. *)
  Admitted.

End main.

Lemma encL_inj l1 l2 :
  encL l1 = encL l2 -> l1 = l2.
Proof.
  induction l1 in l2 |- *; intros H.
  - destruct l2; cbn in *; congruence.
  - destruct l2; cbn in *; try congruence.
    inversion H. f_equal; eauto.
    destruct a, b; now inversion H1.
Qed.

Lemma L_computable_function {k} R :
  @L_computable k R -> functional R.
Proof.
  intros [s Hs] v m1 m2 H1 H2.
  eapply Hs in H1. eapply Hs in H2.
  rewrite eval_iff in H1, H2.
  destruct H1 as [H1 H1'], H2 as [H2 H2'].
  eapply encL_inj, L_facts.unique_normal_forms; eauto.
  now rewrite <- H1, H2.
Qed.

Lemma Vector_hd_nth {k X} (v : Vector.t X (S k)) :
  Vector.hd v = v[@Fin0].
Proof.
  dependent destruct v. reflexivity.
Qed.

Theorem compiler_bool {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) :
  L_computable R -> TM_computable R.
Proof.
  intros H. 
  eapply TM_computable_rel'_spec.
  eapply L_computable_function; eauto.
  eapply L_computable'_spec in H as [sim Hsim].
  exists n_main, Σ, sym_s, sym_b. split. eapply syms_diff. exists (M_main k sim). split.
  - eapply Realise_monotone. { eapply M_main_realise. eapply Hsim. intros. now eapply Hsim. }
    intros t [[] t'] H v ->.
    destruct (H v) as [m [Hm1 Hm2]]. reflexivity.
    exists m. split; eauto. rewrite <- Hm1.
    eapply Vector_hd_nth.
  - admit.
Admitted.
