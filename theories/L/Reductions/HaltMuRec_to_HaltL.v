Set Default Goal Selector "!".

From Undecidability.H10 Require Import H10 dio_single dio_logic.
From Undecidability.L.Datatypes Require Import LNat LOptions LSum.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared Require Import DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import MuRec recalg ra_sem_eq.
From Undecidability.MuRec.Util Require Import eval.


From Undecidability Require Import MuRec_computable LVector.
From Undecidability.L.Util Require Import NaryApp.

Import L_Notations.

Definition cont_vec (k : nat) : term := lam (many_lam k (k (Vector.fold_right (fun n s => (ext (@cons nat) (var n)) s) (many_vars k)  (ext (@nil nat))))).

Lemma helper_closed k :
  bound k (Vector.fold_right (fun (n : nat) (s0 : term) => ext (@cons nat) n s0) (many_vars k) (ext (@nil nat))).
Proof.
  induction k.
  - cbn. cbv. repeat econstructor.
  - rewrite many_vars_S. cbn. econstructor. 1: econstructor. 1: eapply closed_dcl_x. 1: Lproc.
    1: econstructor; lia.
    eapply bound_ge. 1: eauto. lia.
Qed.

Lemma subst_closed s n u :
  closed s -> subst s n u = s.
Proof.
  now intros ->.
Qed.

Lemma vector_closed:
  forall (k : nat) (v : Vector.t nat k) (x : term), Vector.In x (Vector.map enc v) -> proc x.
Proof.
  intros k v.
  induction v; cbn; intros ? Hi. 1: inversion Hi. inv Hi. 1:Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. 1:subst; eauto. eapply nat_eq_dec.
Qed.

Lemma equiv_R (s t t' : term):
  t == t' -> s t == s t'.
Proof.
  now intros ->.
Qed.

Lemma cont_vec_correct k s (v : Vector.t nat k) :
  proc s ->
  many_app (cont_vec k s) (Vector.map enc v) == s (enc v).
Proof.
  intros Hs.
  unfold cont_vec.
  rewrite equiv_many_app_L.
  2:{ eapply beta_red. 1:Lproc. rewrite subst_many_lam. replace (k + 0) with k by lia. reflexivity. }
  cbn -[plus mult]. rewrite Nat.eqb_refl.
  rewrite bound_closed_k. 2:eapply helper_closed.
  replace (3 * k) with (k + 2 * k) by lia.
  etransitivity.
  { apply many_beta. eapply vector_closed. }
  rewrite many_subst_app.
  rewrite many_subst_closed. 2:Lproc.
  replace (2 * k) with (2 * k + 0) by lia.
  eapply equiv_R.
  induction v.
  - cbn. reflexivity.
  - rewrite many_vars_S. cbn -[mult]. rewrite subst_closed; [ | now Lproc].
    rewrite Nat.eqb_refl.
    rewrite !many_subst_app.
    repeat (rewrite many_subst_closed; [ | now Lproc]).
    rewrite bound_closed_k. 2:eapply helper_closed. rewrite IHv.
    rewrite !enc_vector_eq.
    now Lsimpl.
Qed.

Definition mu_option : term := (lam (0 (mu (lam (1 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0))).

Lemma mu_option_proc : proc mu_option.
Proof.
  unfold mu_option. Lproc.
Qed.
#[export] Hint Resolve mu_option_proc : Lproc.

From Undecidability Require Import LOptions.

Lemma mu_option_equiv {X} `{encodable X} s (b : X)  :
  proc s ->
  mu_option s == s (mu (lam (s 0 (lam (enc true)) (enc false)))) (lam 0) (lam 0).
Proof.
  unfold mu_option. intros Hs. now Lsimpl.
Qed.

Definition mu_option_spec {X} {ENC : encodable X} {I : encInj ENC} s (b : X)  :
  proc s ->
  (forall x : X, enc x <> lam 0) ->
 (forall n : nat, exists o : option X, s (enc n) == enc o) ->
  (forall b : X, forall m n : nat, s (enc n) == enc (Some b) -> m >= n -> s (enc m) == enc (Some b)) ->
  mu_option s == enc b <-> exists n : nat, s (enc n) == enc (Some b).
Proof.
  intros Hs Hinv Ht Hm.
  rewrite (@mu_option_equiv X); eauto.
  split.
  - intros He.
    match goal with [He : ?s == _ |- _ ] => assert (converges s) as Hc end.
    { eexists. split. 1: exact He. Lproc. }
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [_ Hc].
    destruct Hc as [v [Hc Hv]].
    pose proof (Hc' := Hc).
    eapply mu_sound in Hc as [n [-> [Hc1 _]]]; eauto.
    * exists n.
      destruct (Ht n) as [ [x | ] Htt].
      -- rewrite Htt. 
         enough (enc b == enc x) as -> % enc_extinj. 1: reflexivity.
         rewrite <- He.
         rewrite Hc'. Lsimpl. rewrite Htt. now Lsimpl.
      -- exfalso. eapply (Hinv b). eapply unique_normal_forms; try Lproc.
         rewrite <- He, Hc'. Lsimpl.
         rewrite Htt. Lsimpl. reflexivity.
    * Lproc.
    * intros n. destruct (Ht n) as [[] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
  - intros [n Hn].
    edestruct mu_complete' with (n := n) as [n' [H' H'']].
    4: rewrite H'.
    + Lproc.
    + intros m. destruct (Ht m) as [ [] ];
      eexists; Lsimpl; rewrite H; Lsimpl; reflexivity.
    + Lsimpl. rewrite Hn. now Lsimpl.
    + destruct (Ht n') as [[] Heq]; rewrite Heq; Lsimpl.
      * enough (HH : enc (Some x) == enc (Some b))by now eapply enc_extinj in HH; inv HH.
        assert (n <= n' \/ n' <= n) as [Hl | Hl] by lia.
        -- eapply Hm in Hl; eauto. now rewrite <- Heq, Hl.
        -- eapply Hm in Hl; eauto. now rewrite <- Hn, Hl.
      * enough (false = true) by congruence.
        eapply enc_extinj. rewrite <- H''.
        symmetry. Lsimpl. rewrite Heq. now Lsimpl.
Qed.

Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.

#[export]
Instance computable_evalfun : computable evalfun.
Proof. extract. Qed.

Lemma vec_list_eq {n X} (v : Vector.t X n) :
  vec_list v = Vector.to_list v.
Proof.
  induction v; cbn; f_equal; eassumption.
Qed.  



Lemma eval_mono c min k (v : Vector.t nat k) (f : recalg k) o :
  eval c min (erase f) (vec_list v) = Some (inl o) -> forall c', c' >= c -> eval c' min (erase f) (vec_list v) = Some (inl o).
Proof.
  intros H c' Hl. eapply erase_correct in H.
  eapply ra_bs_mono in H. 2: eauto.
  now eapply erase_correct in H.
Qed.

Lemma many_app_eq_nat {k} (v : Vector.t nat k) s :  many_app s (Vector.map enc v) = Vector.fold_left (fun (s : term) n => s (nat_enc n)) s v.
Proof.
   induction v in s |- *.
   * cbn. reflexivity.
   * cbn. now rewrite IHv.
Qed.

Theorem computable_MuRec_to_L {k} (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R -> L_computable R.
Proof.
  intros [f Hf].
  exists (cont_vec k (lam (mu_option (lam (ext evalfun 0 (enc (erase f)) 1))))).
  intros v. rewrite <- many_app_eq_nat. split.
  - intros m. rewrite L_facts.eval_iff.
    assert (lambda (nat_enc m)) as [b Hb]. { change  (lambda (enc m)). Lproc. }
    rewrite Hb. rewrite eproc_equiv. rewrite cont_vec_correct. 2: unfold mu_option; Lproc.
    assert (lam (mu_option (lam (ext evalfun 0 (enc (erase f)) 1))) (enc v) ==
          mu_option (lam (ext evalfun 0 (enc (erase f)) (enc v)))).
    {  unfold mu_option. now Lsimpl. }
    rewrite H. rewrite <- Hb.
    change (nat_enc m) with (enc m).
    rewrite mu_option_spec. 2:Lproc.
    2:{ intros []; cbv; congruence. }
    2:{ intros. eexists. rewrite !enc_vector_eq. Lsimpl. reflexivity. }
    1: rewrite Hf.
    1: split.
    + intros [n Hn % erase_correct] % ra_bs_to_c. exists n.
      rewrite !enc_vector_eq. Lsimpl.
      unfold evalfun. rewrite <- vec_list_eq. now rewrite Hn.
    + intros [n Hn]. eapply ra_bs_from_c. eapply erase_correct with (c := n).
      match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
      { rewrite !enc_vector_eq. Lsimpl. subst t. reflexivity. } subst t.
      rewrite vec_list_eq. rewrite H0 in Hn. eapply enc_extinj in Hn.
      unfold evalfun in Hn. now destruct eval as [[] | ]; inv Hn.
    + intros. rewrite enc_vector_eq in *.
      match type of H0 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity. rewrite H2 in H0. clear H2.
      eapply enc_extinj in H0. Lsimpl.
      unfold evalfun in *.
      destruct (eval n) as [ [] | ] eqn:E; inv H0.
      rewrite <- vec_list_eq in *.
      eapply eval_mono in E. 1: rewrite E; eauto. lia.
  - intros v' [H1 H2] % eval_iff.
    eapply star_equiv_subrelation in H1.
    rewrite cont_vec_correct in H1. 2: unfold mu_option; Lproc.
    match goal with [Hn : ?s == ?b |- _ ] => evar (t : term); assert (s == t) end.
    1: unfold mu_option. 1: Lsimpl. all: subst t. 1: reflexivity.
    rewrite H in H1.
    match type of H1 with ?s == _ => assert (converges s) end.
    1: exists v'; split; eassumption.
    eapply app_converges in H0 as [Hc _].
    eapply app_converges in Hc as [Hc _].
    eapply app_converges in Hc as [_ Hc].
    destruct Hc as [v'' [Hc1 Hc2]].
    pose proof (Hc1' := Hc1).
    eapply mu_sound in Hc1; eauto.
    + destruct Hc1 as [m [-> []]].
      rewrite Hc1' in H1.
      rewrite enc_vector_eq in H1.
      destruct (evalfun m (erase f) (Vector.to_list v)) eqn:E.
      * match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H4, E in H1.
      match type of H1 with ?s == ?b => evar (t : term); assert (s == t) end. 1: Lsimpl. all: subst t. 1: reflexivity.
      rewrite H5 in H1.
      eapply unique_normal_forms in H1. 2,3: Lproc.
      subst. exists n. reflexivity.
      * enough (true = false) by congruence. eapply enc_extinj.
        rewrite <- H0. rewrite enc_vector_eq. Lsimpl.
        now rewrite E.
    + Lproc.
    + intros n.
      destruct (evalfun n (erase f) (Vector.to_list v)) eqn:EE;
      eexists; rewrite enc_vector_eq; Lsimpl; rewrite EE; try Lsimpl; reflexivity.
Qed.

Definition UMUREC_HALTING c := exists fuel, evalfun fuel c nil <> None.

Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Lemma MUREC_red : recalg.MUREC_HALTING ⪯ UMUREC_HALTING.
Proof.
  unshelve eexists.
  - intros f. exact (erase f).
  - unfold UMUREC_HALTING, MUREC_HALTING. 
    intros f.
    split; intros [].
    + rewrite ra_bs_correct in H. eapply ra_bs_to_c in H as [].
      exists x0. eapply erase_correct in H. unfold evalfun. cbn in H. rewrite H. congruence.
    + unfold evalfun in H. destruct eval eqn:E; try congruence.
      destruct s; try congruence.
      eapply erase_correct with (v := vec_nil) in E.
      exists n. eapply ra_bs_correct. now eapply ra_bs_from_c.
Qed.

Local Definition r := (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).

Lemma MUREC_WCBV : MUREC_HALTING ⪯ converges.
Proof.
  eapply reduces_transitive. 1:eapply MUREC_red.
  eapply L_recognisable_halt.
  exists (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).
  split.
  - econstructor. extract.
  - firstorder.
    + unfold evalfun in *. exists x0. destruct eval; try destruct s; try congruence.
    + exists x0. unfold evalfun in *. destruct eval; try destruct s; try congruence.
Qed.
