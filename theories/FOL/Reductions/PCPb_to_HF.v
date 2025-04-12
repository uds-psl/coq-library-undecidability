(* ** Reduction from PCP to semantic entailment in finite ZF *)

Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FullFacts.
Require Import Undecidability.FOL.Sets.ZF.
Require Undecidability.FOL.Sets.Models.HF_model.
From Stdlib Require Import Lia.

From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* ** Reduction function *)

Local Definition BSRS := list(card bool).

Fixpoint shift n x :=
  match n with 
  | O => x
  | S n => subst_term ↑ (shift n x)
  end.

Definition sing a :=
  {a; a}.

Definition opair a b :=
  {{a; a}; {a; b}}.

Definition pairing f A :=
  ∀ $0 ∈ shift 1 f → ∃ ∃ $1 ∈ shift 3 A ∧ $2 ≡ opair $1 $0.

Definition function' f A :=
  pairing f A ∧ ∀ ∃ $0 ∈ shift 2 A ∧ opair $0 $1 ∈ shift 2 f
                    ∧ ∀ opair $1 $0 ∈ shift 2f → $2 ≡ $0.

Definition function f :=
  ∀ ∀ ∀ opair $2 $1 ∈ shift 3 f → opair $2 $0 ∈ shift 3 f → $1 ≡ $0.

Definition enc_bool (x : bool) :=
  if x then {∅; ∅} else ∅.

Fixpoint prep_string (s : string bool) a :=
  match s with
  | nil => a
  | b::s => opair (enc_bool b) (prep_string s a)
  end.

Definition enc_string (s : string bool) :=
  prep_string s ∅.

Fixpoint enc_stack (B : BSRS) :=
  match B with
  | nil => ∅
  | (s,t)::B => enc_stack B ∪ sing (opair (enc_string s) (enc_string t))
  end.

Definition is_rep phi a b :=
  ∀ $0 ∈ shift 1 b ↔ ∃ $0 ∈ shift 2 a ∧ phi.

Definition comb_rel s t :=
  ∃ ∃ $2 ≡ opair $0 $1 ∧ $3 ≡ opair (prep_string s $0) (prep_string t $1).

Fixpoint combinations (B : BSRS) a b :=
  match B with
  | nil => b ≡ ∅
  | (s,t)::B => ∃ ∃ shift 2 b ≡ $0 ∪ $1 ∧ combinations B (shift 2 a) $1
                   ∧ is_rep (comb_rel s t) (shift 2 a) $0
  end.

Definition solutions (B : BSRS) f n :=
  opair ∅ (enc_stack B) ∈ f ∧ ∀ ∀ ∀ $2 ∈ shift 3 n → opair $2 $1 ∈ shift 3 f
               → combinations B $1 $0 → opair (σ $2) $0 ∈ shift 3 f.

Definition transitive t :=
  ∀ $0 ∈ shift 1 t → $0 ⊆ shift 1 t.

Definition htransitive t :=
  transitive t ∧ ∀ $0 ∈ shift 1 t → transitive $0.

Definition solvable (B : BSRS) :=
  ∃ ∃ ∃ ∃ htransitive $3 ∧ function $2 ∧ solutions B $2 $3 ∧ opair $3 $0 ∈ $2 ∧ opair $1 $1 ∈ $0.

Lemma bool_bound b n :
  bounded_t n (enc_bool b).
Proof.
  destruct b; repeat solve_bounds.
Qed.

Lemma prep_string_bound s t n :
  bounded_t n t -> bounded_t n (prep_string s t).
Proof.
  intros Ht. induction s; cbn; trivial.
  repeat solve_bounds; trivial.
  all: apply bool_bound.
Qed.

Lemma string_bound s n :
  bounded_t n (enc_string s).
Proof.
  apply prep_string_bound. solve_bounds.
Qed.

Lemma stack_bound B n :
  bounded_t n (enc_stack B).
Proof.
  induction B as [|[s t] B IH]; cbn; repeat solve_bounds; trivial.
  all: apply string_bound.
Qed.

Lemma combinations_bound (B : BSRS) n k l :
  n > 2 + l -> n > 4 + k -> bounded n (combinations B $k $l).
Proof.
  revert n k l. induction B as [|[s t] B IH]; cbn; intros n k l H1 H2; solve_bounds.
  apply IH; lia. all: apply prep_string_bound; solve_bounds.
Qed.

Lemma solvabe_bound B :
  bounded 0 (solvable B).
Proof.
  repeat solve_bounds.
  - apply stack_bound.
  - apply combinations_bound; lia.
Qed.
  

Import HF_model.


Section ZF.

  Context { V : Type }.
  Context { M : interp V }.

  Hypothesis M_ZF : forall rho, rho ⊫ HF.
  Hypothesis VIEQ : extensional M.

  Notation binunion_el := (@binunion_el _ _ M_ZF VIEQ).
  Notation sing_el := (@sing_el _ _ M_ZF VIEQ).
  Notation M_pair := (@M_pair _ _ M_ZF VIEQ).
  Notation opair_inj := (@opair_inj _ _ M_ZF VIEQ).
  Notation binunion_com := (@binunion_com _ _ M_ZF VIEQ).
  Notation binunion_assoc := (@binunion_assoc _ _ M_ZF VIEQ).
  Notation sigma_el := (@sigma_el _ _ M_ZF VIEQ).
  Notation sigma_eq := (@sigma_eq _ _ M_ZF VIEQ).
  Notation numeral_inj := (@numeral_inj _ _ M_ZF VIEQ).
  Notation M_ext := (@M_ext _ _ M_ZF VIEQ).
  Notation M_eset := (@M_eset _ _ M_ZF VIEQ).
  Notation numeral_htrans := (@numeral_htrans _ _ M_ZF VIEQ).
  Notation binunion_eset := (@binunion_eset _ _ M_ZF VIEQ).

  (* ** Encodings *)

  (* Encodings of booleans, strings, cards, and stacks *)

  Definition M_enc_bool (x : bool) :=
    if x then {∅; ∅} else ∅.

  Fixpoint M_prep_string (s : string bool) x :=
    match s with
    | nil => x
    | b::s => M_opair (M_enc_bool b) (M_prep_string s x)
    end.

  Definition M_enc_string (s : string bool) :=
    M_prep_string s ∅.

  Definition M_enc_card s t :=
    M_opair (M_enc_string s) (M_enc_string t).

  Fixpoint M_enc_stack (B : BSRS) :=
    match B with
    | nil => ∅
    | (s,t)::B => M_enc_stack B ∪ M_sing (M_enc_card s t)
    end.

  (* Injectivity of encodings *)

  Lemma enc_bool_inj b c :
    M_enc_bool b = M_enc_bool c -> b = c.
  Proof using M_ZF VIEQ.
    destruct b, c; trivial; cbn.
    - intros H. contradiction (@M_eset ∅).
      pattern ∅ at 2. rewrite <- H. apply M_pair; auto.
    - intros H. contradiction (@M_eset ∅).
      pattern ∅ at 2. rewrite H. apply M_pair; auto.
  Qed.

  Lemma enc_string_inj s t :
    M_enc_string s = M_enc_string t -> s = t.
  Proof using M_ZF VIEQ.
    induction s in t|-*; destruct t as [|b t]; cbn; trivial.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool b))).
      rewrite H. apply M_pair. now left.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool a))).
      rewrite <- H. apply M_pair. now left.
    - intros [H1 H2] % opair_inj. apply IHs in H2 as ->.
      apply enc_bool_inj in H1 as ->. reflexivity.
  Qed.

  (* Agreement to syntactical encodings under evaluation *)

  Lemma eval_opair rho x y :
    eval rho (opair x y) = M_opair (eval rho x) (eval rho y).
  Proof using M_ZF VIEQ.
    reflexivity.
  Qed.

  Lemma eval_enc_bool rho b :
    eval rho (enc_bool b) = M_enc_bool b.
  Proof using M_ZF VIEQ.
    destruct b; reflexivity.
  Qed.

  Lemma eval_prep_string rho s x :
    eval rho (prep_string s x) = M_prep_string s (eval rho x).
  Proof using M_ZF VIEQ.
    induction s; trivial. cbn [prep_string].
    now rewrite eval_opair, IHs, eval_enc_bool.
  Qed.

  Lemma eval_enc_string rho s :
    eval rho (enc_string s) = M_enc_string s.
  Proof using M_ZF VIEQ.
    unfold enc_string. now rewrite eval_prep_string.
  Qed.
  
  Lemma eval_enc_stack rho B :
    eval rho (enc_stack B) = M_enc_stack B.
  Proof using M_ZF VIEQ.
    induction B; cbn; trivial. destruct a. unfold M_enc_card.
    now rewrite <- IHB, <- !eval_enc_string with (rho:=rho), <- eval_opair.
  Qed.

  (* Auxiliary lemmas for stack encodings *)

  Lemma M_enc_stack_app A B :
    M_enc_stack (A ++ B) = M_enc_stack A ∪ M_enc_stack B.
  Proof using M_ZF VIEQ.
    induction A as [|[s t] A IH]; cbn.
    - apply binunion_eset.
    - rewrite IH. rewrite !binunion_assoc.
      now rewrite (binunion_com (M_enc_stack B) (M_sing (M_enc_card s t))).
  Qed.

  Lemma enc_stack_el' x A :
    x ∈ M_enc_stack A -> exists s t, (s, t) el A /\ x = M_enc_card s t.
  Proof using M_ZF VIEQ.
    induction A as [|[s t] A IH]; cbn.
    - now intros H % M_eset.
    - intros [H|H] % binunion_el.
      + destruct (IH H) as (u&v&H'&->). exists u, v. intuition.
      + apply sing_el in H as ->. exists s, t. intuition.
  Qed.

  Lemma enc_stack_el B s t :
    (s, t) el B -> M_enc_card s t ∈ M_enc_stack B.
  Proof using M_ZF VIEQ.
    induction B as [|[u b] B IH]; cbn; auto.
    intros [H|H]; apply binunion_el.
    - right. apply sing_el. congruence.
    - left. apply IH, H.
  Qed.

  Lemma M_prep_enc s s' :
    M_prep_string s (M_enc_string s') = M_enc_string (s ++ s').
  Proof using M_ZF VIEQ.
    induction s; cbn; trivial.
    now rewrite IHs.
  Qed.



  (* ** Preservation direction *)

  (*
     We encode the k-step solutions of a PCP instance B as a set-theoretic function M_enc_derivations.
     This function satisfies the conditions expressed in the reduction formula and
     contains a solution whenever B is solvable.
   *)
     
  Definition append_all A (c : card bool) :=
    map (fun p => (fst c ++ fst p, snd c ++ snd p)) A.

  Definition derivation_step B C :=
    flat_map (append_all C) B.

  Fixpoint derivations B n :=
    match n with
    | O => B
    | S n => derivation_step B (derivations B n)
    end.

  Lemma derivable_derivations B s t :
    derivable B s t -> exists n, (s, t) el derivations B n.
  Proof.
    induction 1.
    - exists 0. apply H.
    - destruct IHderivable as [n Hn]. exists (S n).
      apply in_flat_map. exists (x, y). split; trivial.
      apply in_map_iff. exists (u,v). cbn. split; trivial.
  Qed.

  Fixpoint M_enc_derivations B n :=
    match n with 
    | O => M_sing (M_opair ∅ (M_enc_stack B))
    | S n => M_enc_derivations B n ∪
            M_sing (M_opair (numeral (S n)) (M_enc_stack (derivations B (S n))))
    end.

  Lemma enc_derivations_base B n :
    M_opair ∅ (M_enc_stack B) ∈ M_enc_derivations B n.
  Proof using M_ZF VIEQ.
    induction n; cbn.
    - now apply sing_el.
    - apply binunion_el. now left.
  Qed.

  Lemma enc_derivations_bound B n k x :
    M_opair k x ∈ M_enc_derivations B n -> k ∈ σ (numeral n).
  Proof using M_ZF VIEQ.
    induction n; cbn.
    - intros H % sing_el. apply opair_inj in H as [-> _].
      apply sigma_el. now right.
    - intros [H|H] % binunion_el.
      + apply sigma_el. left. apply IHn, H.
      + apply sing_el in H. apply opair_inj in H as [-> _]. apply sigma_eq.
  Qed. 

  Lemma enc_derivations_fun B n :
    forall k x y, M_opair k x ∈ M_enc_derivations B n -> M_opair k y ∈ M_enc_derivations B n -> x = y.
  Proof using M_ZF VIEQ.
    induction n; cbn -[derivations]; intros k x y.
    - intros H1 % sing_el H2 % sing_el.
      rewrite <- H2 in H1. now apply opair_inj in H1.
    - intros [H1|H1 % sing_el] % binunion_el [H2|H2 % sing_el] % binunion_el.
      + now apply (IHn k x y).
      + exfalso. apply enc_derivations_bound in H1.
        destruct (opair_inj H2) as [-> _]. now apply (@numeral_wf _ _ M_ZF VIEQ (S n)).
      + exfalso. apply enc_derivations_bound in H2.
        destruct (opair_inj H1) as [-> _]. now apply (@numeral_wf _ _ M_ZF VIEQ (S n)).
      + rewrite <- H2 in H1. now apply opair_inj in H1.
  Qed.

  Lemma enc_derivations_el B n k x :
    M_opair k x ∈ M_enc_derivations B n -> exists l, k = numeral l /\ x = M_enc_stack (derivations B l).
  Proof using M_ZF VIEQ.
    induction n; cbn.
    - intros H % sing_el. exists 0. apply (opair_inj H).
    - intros [H|H] % binunion_el.
      + apply IHn, H.
      + apply sing_el in H. exists (S n). apply (opair_inj H).
  Qed. 

  Lemma enc_derivations_step B n l :
    numeral l ∈ numeral n
    -> M_opair (σ (numeral l)) (M_enc_stack (derivations B (S l))) ∈ M_enc_derivations B n.
  Proof using M_ZF VIEQ.
    induction n; cbn -[derivations].
    - now intros H % M_eset.
    - intros [H|H % sing_el] % binunion_el; apply binunion_el.
      + left. apply IHn, H.
      + right. apply numeral_inj in H as ->. now apply sing_el.
  Qed.

  Lemma enc_stack_combinations B rho C x X Y :
    rho ⊨ combinations B X Y -> eval rho X = M_enc_stack C -> eval rho Y = x -> x = M_enc_stack (derivation_step B C).
  Proof using M_ZF VIEQ.
    induction B as [|[s t] B IH] in rho,C,x,X,Y |-*.
    - cbn. rewrite VIEQ. now intros -> _ <-.
    - intros [x1[x2[[H1 H2]H3]]] R1 R2; fold sat in *.
      assert (x = x2 ∪ x1) as ->. { rewrite <- R2. cbn in H1. rewrite !eval_comp in H1. apply VIEQ, H1. } clear H1.
      cbn. fold (derivation_step B C). rewrite M_enc_stack_app.
      enough (x1 = M_enc_stack (derivation_step B C)) as E1.
      + enough (x2 = M_enc_stack (append_all C (s, t))) as E2 by now rewrite E1, E2.
        apply M_ext; intros u Hu.
        * apply H3 in Hu as [v [Hv[a [b Ha]]]].
          cbn in Hv. erewrite !eval_comp, eval_ext, R1 in Hv; trivial.
          apply enc_stack_el' in Hv as (s'&t'&H&H').
          enough (u = M_enc_card (s++s') (t++t')) as ->.
          { apply enc_stack_el. apply in_map_iff. now exists (s', t'). }
          cbn in Ha. rewrite !VIEQ in Ha. destruct Ha as [D1 D2].
          rewrite D1 in H'. unfold M_enc_card in H'. apply opair_inj in H' as [-> ->].
          rewrite D2; unfold M_enc_card, M_opair; repeat f_equal.
          all: rewrite eval_prep_string; cbn. all: apply M_prep_enc.
        * apply enc_stack_el' in Hu as (s'&t'&H&->).
          unfold append_all in H. eapply in_map_iff in H as [[a b][H H']].
          cbn in H. apply H3. exists (M_enc_card a b). split.
          { cbn. erewrite !eval_comp, eval_ext, R1; trivial. now apply enc_stack_el. }
          exists (M_enc_string b), (M_enc_string a). split.
          -- cbn. apply VIEQ. reflexivity.
          -- cbn. apply VIEQ. rewrite !eval_prep_string. cbn.
             rewrite !M_prep_enc. injection H. intros -> ->. reflexivity.
      + eapply IH; eauto. unfold shift. now erewrite !eval_comp, eval_ext, R1.
  Qed.

  Lemma enc_derivations_solutions B n rho a b :
    (a .: b .: M_enc_derivations B n .: numeral n .: rho) ⊨ solutions B $2 $3.
  Proof using M_ZF VIEQ.
    cbn. split.
    - rewrite eval_enc_stack. apply enc_derivations_base.
    - intros k x x' H1 H2 H3.
      destruct (enc_derivations_el H2) as [l[-> ->]].
      specialize (enc_derivations_step B H1).
      replace (M_enc_stack (derivations B (S l))) with x'; trivial.
      apply (enc_stack_combinations H3); trivial.
  Qed.

  Lemma derivations_enc_derivations B n :
    M_opair (numeral n) (M_enc_stack (derivations B n)) ∈ M_enc_derivations B n.
  Proof using M_ZF VIEQ.
    induction n; cbn -[derivations].
    - now apply sing_el.
    - apply binunion_el. right.
      now apply sing_el.
  Qed.

  Lemma derivations_el B n s t :
    (s, t) el derivations B n -> M_enc_card s t ∈ M_enc_stack (derivations B n).
  Proof using M_ZF VIEQ.
    apply enc_stack_el.
  Qed.

  Theorem PCP_HF1 B s :
    derivable B s s -> forall rho, rho ⊨ solvable B.
  Proof using M_ZF VIEQ.
    intros H rho. destruct (derivable_derivations H) as [n Hn]. unfold solvable.
    exists (numeral n), (M_enc_derivations B n), (M_enc_string s), (M_enc_stack (derivations B n)).
    split; [split; [split; [split |] |] |].
    - apply numeral_htrans.
    - unfold function'. intros k x y H1 H2. apply VIEQ. apply (enc_derivations_fun H1 H2).
    - apply enc_derivations_solutions.
    - cbn. apply derivations_enc_derivations.
    - now apply enc_stack_el.
  Qed.



  (* ** Reflection direction *)

  (*
    Conversely, we show how to reconstruct a solution of a PCP instance B from a model
    (1) satisfying the reduction formula defined above and
    (2) containing only the standard natural numers.
    The latter seems necessary to exclude non-standard solutions the model might contain.
   *)
    
  Definition M_comb_rel s t :=
    fun u v => exists u1 u2, u = M_opair u1 u2 /\ v = M_opair (M_prep_string s u1) (M_prep_string t u2).

  Fixpoint M_combinations B x y :=
    match B with
    | nil => y = ∅
    | (s,t)::B => exists y1 y2, y = y2 ∪ y1 /\ M_combinations B x y1 /\ M_is_rep (M_comb_rel s t) x y2
    end.

  Lemma M_combinations_spec B rho x y a b :
    M_combinations B x y -> eval rho a = x -> eval rho b = y -> rho ⊨ combinations B a b.
  Proof using M_ZF VIEQ.
    induction B in y,a,b,rho|-*; cbn.
    - rewrite VIEQ. now intros -> _ ->.
    - destruct a0 as [s t]. intros (y1&y2&H1&H2&H3) Ha Hb. exists y1, y2. repeat split.
      + cbn. apply VIEQ. erewrite !eval_comp. unfold funcomp. cbn.
        change (eval (fun x => rho x) b) with (eval rho b). now rewrite Hb.
      + eapply (IHB _ y1); trivial. erewrite !eval_comp. unfold funcomp. cbn.
        change (eval (fun x => rho x) a) with (eval rho a). now rewrite Ha.
      + intros (u & Hu & c & d' & H) % H3. exists u. split.
        * cbn. erewrite !eval_comp. erewrite eval_ext, Ha; trivial.
        * exists d', c. cbn. rewrite !VIEQ, !eval_prep_string. apply H.
      + intros (u & Hu & c & d' & H). apply H3. exists u. split.
        * cbn in Hu. erewrite !eval_comp in Hu. rewrite <- Ha. apply Hu.
        * exists d', c. cbn in H. rewrite !VIEQ, !eval_prep_string in H. apply H.
  Qed.

  Definition M_solutions B f n :=
    M_opair ∅ (M_enc_stack B) ∈ f /\ forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f.

  Lemma comb_rel_rep C s t :
    M_is_rep (M_comb_rel s t) (M_enc_stack C) (M_enc_stack (append_all C (s, t))).
  Proof using M_ZF VIEQ.
    intros y. split.
    - intros (u&v&H&->) % enc_stack_el'.
      unfold append_all in H. apply in_map_iff in H as [[a b][H1 H2]]. cbn in H1.
      exists (M_enc_card a b). split; try now apply enc_stack_el.
      exists (M_enc_string a), (M_enc_string b). split; trivial.
      assert (u = s++a) as -> by congruence. assert (v = t++b) as -> by congruence.
      now rewrite !M_prep_enc.
    - intros (u&H&a&b&->&->). apply enc_stack_el' in H as [u[v[H1 H2]]].
      apply opair_inj in H2 as [-> ->]. rewrite !M_prep_enc. apply enc_stack_el.
      apply in_map_iff. now exists (u, v).
  Qed.

  Lemma M_combinations_step B C :
    M_combinations B (M_enc_stack C) (M_enc_stack (derivation_step B C)).
  Proof using M_ZF VIEQ.
    induction B as [|[s t] B IH]; cbn; trivial.
    exists (M_enc_stack (derivation_step B C)), (M_enc_stack (append_all C (s, t))).
    rewrite M_enc_stack_app. split; trivial. split; trivial.
    apply comb_rel_rep.
  Qed.

  Lemma solutions_derivations B f n k :
    M_solutions B f (numeral n) -> k <= n -> M_opair (numeral k) (M_enc_stack (derivations B k)) ∈ f.
  Proof using M_ZF VIEQ.
    intros H Hk; induction k; cbn.
    - apply H.
    - assert (Hk' : k <= n) by lia. specialize (IHk Hk').
      destruct H as [_ H]. eapply H in IHk; eauto.
      + now apply numeral_lt.
      + apply M_combinations_step.
  Qed.

  Lemma derivations_derivable B n s t :
    (s, t) el derivations B n -> derivable B s t.
  Proof using M_ZF VIEQ.
    induction n in s,t|-*; cbn.
    - now constructor.
    - unfold derivation_step. intros [[u v][H1 H2]] % in_flat_map.
      unfold append_all in H2. apply in_map_iff in H2 as [[a b][H2 H3]]. cbn in H2.
      assert (s = u++a) as -> by congruence. assert (t = v++b) as -> by congruence.
      constructor 2; trivial. apply IHn, H3.
  Qed.

  Definition M_function f :=
    forall x y y', M_opair x y ∈ f -> M_opair x y' ∈ f -> y = y'.

  Lemma M_solutions_el B f k X p :
    standard M -> htrans k -> M_function f -> M_solutions B f k -> M_opair k X ∈ f
    -> p ∈ X -> exists u v, p = M_enc_card u v /\ derivable B u v.
  Proof using M_ZF VIEQ.
    intros HS HO Hf Hk HX Hp. destruct (HS k HO) as [n -> % VIEQ].
    pose proof (H := solutions_derivations Hk (le_n n)).
    rewrite (Hf _ _ _ HX H) in Hp. apply enc_stack_el' in Hp as (s&t&H'&->).
    exists s, t. split; trivial. eapply derivations_derivable; eauto.
  Qed.

  Theorem PCP_HF2 B rho :
    standard M -> rho ⊨ solvable B -> exists s, derivable B s s.
  Proof using M_ZF VIEQ.
    intros VIN (n & f & s & X & [[[[H1 H2] H3] H4] H5]).
    assert (H1' : htrans n) by apply H1. clear H1.
    assert (H4' : M_opair n X ∈ f) by apply H4. clear H4.
    assert (H5' : M_opair s s ∈ X) by apply H5. clear H5.
    assert (H2' : M_function f).
    { intros x y y' H H'. apply VIEQ. eapply H2. apply H. apply H'. } clear H2.
    assert (H3' : M_opair ∅ (M_enc_stack B) ∈ f).
    { erewrite <- eval_enc_stack. apply H3. } destruct H3 as [_ H3].
    assert (H3'' : forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f).
    { intros k x y Hn Hk Hy. apply (H3 k x y); auto. fold sat. eapply M_combinations_spec; eauto. } clear H3.
    destruct (@M_solutions_el B f n X (M_opair s s)) as (u&v&H1&H2); trivial.
    now split. exists u. apply opair_inj in H1 as [H ->]. apply enc_string_inj in H as ->. apply H2.
  Qed.
  
End ZF.



(* ** Reduction Theorem *)


Theorem PCP_HF B :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ HF)
  -> PCPb B <-> entailment_HF (solvable B).
Proof.
  intros HZF. rewrite PCPb_iff_dPCPb. split; intros H.
  - clear HZF. destruct H as [s H]. intros M HM rho H1 H2. eapply PCP_HF1; eauto.
  - destruct HZF as (M & H1 & H2 & H3 & H4).
    specialize (H M H1 (fun _ => @i_func _ _ _ _ eset Vector.nil) H2 H4).
    apply PCP_HF2 in H as [s Hs]; trivial. now exists s.
Qed.
