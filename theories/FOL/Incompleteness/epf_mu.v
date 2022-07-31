From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.

From Undecidability.H10 Require Import DPRM dio_single.

From Equations Require Import Equations.
Require Import String List.
From Undecidability.L.Reductions Require Import MuRec.
From Undecidability.MuRec Require Import recalg.
Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.
From Undecidability.H10 Require Import DPRM.
Require Import Undecidability.Synthetic.EnumerabilityFacts.
From Coq.Logic Require Import ConstructiveEpsilon.
From Undecidability.FOL.Incompleteness Require Import utils epf recalg fol qdec sigma1.

Import ListNotations.



Definition mu_semi_decidable (P : nat -> Prop) := 
  exists f : recalg 1, forall x : nat,
    P x <-> (exists y, ra_rel f (Vector.cons nat x 0 (Vector.nil nat)) y).

(* Construct an embedding nat -> recalg 1 *)
Section recalg_enum.
  Definition nat_recalg' : nat -> option (recalg 1) := projT1 (enumeratorT_recalg 1).
  Definition nat_recalg : nat -> recalg 1.
  Proof.
    intros c. destruct (nat_recalg' c).
    - exact r.
    - exact ra_zero.
  Defined.
  Definition recalg_nat : recalg 1 -> nat.
  Proof.
    intros c. destruct (constructive_indefinite_ground_description_nat_Acc (fun n => nat_recalg n = c)) as [y _].
    - intros n. apply recalg_dec.
    - destruct (projT2 (enumeratorT_recalg 1) c) as [x H]. 
      exists x. unfold nat_recalg, nat_recalg'. now rewrite H.
    - exact y.
  Defined.
  Lemma nat_recalg_nat r : nat_recalg (recalg_nat r) = r.
  Proof. 
    unfold nat_recalg, recalg_nat. now destruct constructive_indefinite_ground_description_nat_Acc.
  Qed.
End recalg_enum.


Lemma erase_ra_rel alg x y :
  (exists k, evalfun k (erase alg) [x] = Some y) <-> 
  ra_rel alg (Vector.cons _ x _ (Vector.nil _)) y.
Proof.
  split.
  - intros [k Hk]. 
    apply ra_bs_c_correct. exists k.
    apply erase_correct. unfold evalfun in Hk.
    cbn. now destruct eval as [[]|].
  - intros H. apply ra_bs_c_correct in H as [k Hk].
    exists k. apply erase_correct in Hk. cbn in Hk.
    unfold evalfun. now destruct eval as [[]|].
Qed.

(* Step indexed execution of mu recursive algorithms *)
Definition mu_step : recalg 1 -> nat -\ nat.
Proof.
  intros c x. unshelve eexists.
  { intros k. exact (evalfun k (erase c) [x]). }
  unfold core_valid.
  intros y1 y2 k1 k2 H1 H2. unfold evalfun in *.
  eapply ra_rel_fun.
  - apply erase_ra_rel. exists k1. eassumption.
  - apply erase_ra_rel. exists k2. eassumption.
Defined.
Definition theta_mu : nat -> nat -\ nat := fun c => mu_step (nat_recalg c).
(** ** Church's thesis for mu-recursive functions *)

Section mu.
  Hypothesis mu_universal : is_universal theta_mu.

  (* Mu semi-decidability implies synthetic enumerability assuming EPFmu *)
  Lemma mu_semi_decidable_enumerable (P : nat -> Prop) :
    enumerable P -> mu_semi_decidable P.
  Proof using mu_universal.
    intros [f Hf]%enumerable_semi_decidable; last apply discrete_nat.

    unfold mu_semi_decidable. unfold semi_decider in Hf.

    unshelve edestruct mu_universal as [c Hc].
    { intros x. unshelve eexists.
      { exact (fun k => if f x k then Some 0 else None). }
      intros y1 y2 k1 k2 H1 H2.
      destruct (f x k1) eqn:Hf1, (f x k2) eqn:Hf2; congruence. }
    cbn in Hc.
    exists (nat_recalg c). intros x. rewrite Hf. split.
    - intros [k Hk]. exists 0.
      apply erase_ra_rel.
      destruct (Hc x 0) as [[k' Hk'] _].
      { exists k. cbn. now rewrite Hk. }
      exists k'. assumption.
    - intros [k Hk]. 
      unfold "▷" in Hc. cbn in Hc.
      apply erase_ra_rel, Hc in Hk as [k' Hk'].
      exists k'. now destruct f.
  Qed.
End mu.




(* Imports down here to avoid clashes between list and substitution notation *)
From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature Robinson NatModel.

Section fol.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.


  Section dprm.
    Existing Instance interp_nat.

    Variable P : nat -> Prop.
    Context `{peirc : peirce}.

    Fixpoint fin_to_n k (n : Fin.t k) : nat.
    Proof.
      destruct n.
      - exact 0.
      - exact (S (fin_to_n _ n0)).
    Defined.
    Lemma fin_to_n_bound k (n : Fin.t k) :
      fin_to_n n <= k.
    Proof.
      induction n; cbn; lia.
    Qed.

    Fixpoint embed_poly n (p : dio_polynomial (Fin.t n) (Fin.t 1)) : term.
    Proof.
      destruct p.
      - exact (num n0).
      - exact $(fin_to_n t).
      - exact $n.
      - destruct d.
        + exact (embed_poly _ p1 ⊕ embed_poly _ p2).
        + exact (embed_poly _ p1 ⊗ embed_poly _ p2).
    Defined.
    Lemma embed_poly_bound n (p : dio_polynomial (Fin.t n) (Fin.t 1)) :
      bounded_t (S n) (embed_poly p).
    Proof.
      induction p; cbn.
      - apply num_bound.
      - constructor. pose proof (fin_to_n_bound v). lia.
      - solve_bounds.
      - destruct d; now solve_bounds.
    Qed.

    Fixpoint vec_pos_default {X : Type} {n : nat} (v : Vector.t X n) (d : nat -> X) k : X
      := match v with
         | Vector.nil => d k
         | Vector.cons x n' v' => match k with 
                                    | 0 => x
                                    | S k' => vec_pos_default v' d k'
                                    end
         end.
    Lemma vec_pos_default_fin {X : Type} {n : nat} (v : Vector.t X n) (f : Fin.t n) (d : nat -> X) :
      vec.vec_pos v f = vec_pos_default v d (fin_to_n f).
    Proof.
      induction f; depelim v; now cbn.
    Qed.

    Lemma vec_pos_default_default {X : Type} {n : nat} (v : Vector.t X n) (m : nat) (d : nat -> X) :
      d m = vec_pos_default v d (m + n).
    Proof.
      induction v; cbn.
      - f_equal. lia.
      - now replace (m + S n) with (S m + n) by lia.
    Qed.

    Lemma embed_eval n (p : dio_polynomial (Fin.t n) (Fin.t 1)) : 
      forall x ρ (v : Vector.t nat n), 
        dp_eval (vec.vec_pos v) (fun _ => x) p = eval (vec_pos_default v (x .: ρ)) (embed_poly p).
    Proof. 
      intros x ρ. induction p; intros w; cbn.
      - now rewrite nat_eval_num.
      - apply vec_pos_default_fin.
      - change n with (0 + n).
        now rewrite <-vec_pos_default_default with (m := 0).
      - destruct d; cbn; now rewrite IHp1, IHp2.
    Qed.

    Lemma vec_pos_default_append n m (v : Vector.t nat n) (w : Vector.t nat m) d k :
      vec_pos_default (Vector.append v w) d k = vec_pos_default v (vec_pos_default w d) k.
    Proof.
      induction v in k |-*; first reflexivity.
      cbn. now destruct k.
    Qed.

    Lemma vec_append1 n (v : Vector.t nat (n+1)) :
      exists k w, v = Vector.append w (Vector.cons k Vector.nil).
    Proof.
      induction n as [|n IHn].
      - do 2 depelim v. now exists h, Vector.nil.
      - cbn in v. depelim v. destruct (IHn v) as (k & w & ->). 
        now exists k, (Vector.cons h w). 
    Qed.

    Lemma sat_exist_times n ρ φ : interp_nat; ρ ⊨ exist_times n φ <-> exists w : Vector.t nat n, interp_nat; (vec_pos_default w ρ) ⊨ φ.
    Proof.
      induction n as [|n IHn] in ρ |-*; cbn.
      - split.
        + intros H. now exists Vector.nil.
        + intros [v H]. now depelim v. 
      - setoid_rewrite IHn. split. 
        + intros (k & w & Hw). replace (S n) with (n + 1) by lia.
          exists (Vector.append w (Vector.cons k Vector.nil)).
          eapply sat_ext; first apply vec_pos_default_append.
          assumption.
        + replace (S n) with (n+1) by lia.
          intros [w Hw]. 
          destruct (vec_append1 w) as (h & w' & ->).
          exists h, w'.
          eapply sat_ext in Hw.
          2: { intros x. symmetry. apply vec_pos_default_append. }
          easy.
    Qed.

    Lemma dprm_definable : dio_rec_single P -> exists φ, Σ1 φ /\ bounded 1 φ /\ forall x ρ, P x <-> interp_nat; (x .: ρ) ⊨ φ.
    Proof.
      unfold dio_rec_single.
      intros (n & p1 & p2 & H).
      exists (exist_times n (embed_poly p1 == embed_poly p2)). repeat apply conj.
      - apply exist_times_Σ1. constructor. apply Qdec_eq.
      - apply bounded_exist_times. 
        all: replace (n + 1) with (S n) by lia.
        solve_bounds; apply embed_poly_bound.
      - intros x ρ. rewrite H. clear H. 
        setoid_rewrite sat_exist_times. 
        setoid_rewrite embed_eval. cbn. reflexivity.
    Qed.

    Theorem mu_recursive_definable : mu_semi_decidable P -> exists φ, Σ1 φ /\ bounded 1 φ /\ forall x ρ, P x <-> interp_nat; (x .: ρ) ⊨ φ.
    Proof.
      intros [r Hr]. apply dprm_definable. do 3 apply DPRM_1. now exists r.
    Qed.
    
  End dprm.
  (** ** Weak representability from DPRM *)
  Section Q_weakly_represents.
    Context `{pei : peirce}.
    Hypothesis mu_universal : is_universal theta_mu.

    Variable P : nat -> Prop.
    Hypothesis Penum : enumerable P. 
    Lemma Q_weak_repr : exists φ, bounded 1 φ /\ Σ1 φ /\ forall x, P x <-> Qeq ⊢ φ[(num x)..].
    Proof.
      destruct mu_recursive_definable with (P := P) as (φ & Hb & HΣ & Hr).
      { now apply mu_semi_decidable_enumerable. }
      exists φ. do 2 (split; first assumption).
      intros x. erewrite Hr. instantiate (1 := fun _ => 0). split.
      - intros H. eapply Σ1_completeness.
        + now apply Σ1_subst.
        + eapply subst_bounded_max; last eassumption.
          intros [|n] Hn; last lia. apply num_bound.
        + intros ρ. rewrite sat_single_nat in H.
          eapply sat_closed; last eassumption.
          eapply subst_bounded_max; last eassumption.
          intros [|k] Hk; apply num_bound + solve_bounds.
      - intros H. rewrite sat_single_nat. eapply Σ1_soundness.
        + apply Σ1_subst, Hb.
        + eapply subst_bounded_max; last eassumption.
          intros [|k] Hk; apply num_bound + solve_bounds.
        + apply H.
    Qed.

  End Q_weakly_represents.
End fol.
