Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import Undecidability.FOL.Reification.GeneralReflection.
Require Import Undecidability.FOL.PA.
Import MetaCoq.Template.Ast MetaCoq.Template.TemplateMonad.Core.
Import Vector.VectorNotations.
Require Import String List.

Section ReificationExample.
  (* We assume an arbitrary model of PA which fulfills the axioms of PA *)
  Context (D':Type).
  Context {I : interp D'}.
  Context {D_fulfills : forall f rho, PAeq f -> rho ⊨ f}.

  Notation "'iO'" := (@i_func _ _ D' I Zero ([])) (at level 1) : PA_Notation.
  Notation "'iS' x" := (@i_func _ _ D' I Succ ([x])) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (@i_func _ _ D' I Plus ([x ; y]) ) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (@i_func _ _ D' I Mult ([x ; y]) ) (at level 38) : PA_Notation.
  Notation "x 'i=' y" := (@i_atom _ _ D' I Eq ([x ; y]) ) (at level 40) : PA_Notation.
  Open Scope string_scope.

  Instance PA_reflector : tarski_reflector := buildDefaultTarski 
                        (iO) (* we need a point in D *)
                        (anyVariableOf ("D'" :: nil)). (* We need to know when some type is D *)

  Lemma ieq_refl d : d i= d.
  Proof. apply (D_fulfills ax_refl (fun _ => iO)). apply PAeq_FA. now left. Qed.
  Lemma ieq_sym d d' : d i= d' -> d' i= d.
  Proof. apply (D_fulfills ax_sym (fun _ => iO)). apply PAeq_FA. right. now left. Qed.
  Lemma ieq_trans d d' d'' : d i= d' -> d' i= d'' -> d i= d''.
  Proof. apply (D_fulfills ax_trans (fun _ => iO)). apply PAeq_FA. do 2 right. now left. Qed.
  Lemma ieq_congr_succ d d' : d i= d' -> iS d i= iS d'.
  Proof. apply (D_fulfills ax_succ_congr (fun _ => iO)). apply PAeq_FA. do 3 right. now left. Qed.
  Lemma ieq_congr_add d d' e e' : d i= d' -> e i= e' -> d i⊕ e i= d' i⊕ e'.
  Proof. apply (D_fulfills ax_add_congr (fun _ => iO)). apply PAeq_FA. do 4 right. now left. Qed.

  (* PA induction lemma: like the usual one for nat, but P has to be representable as a first-order term *)
  Lemma PA_induction (P:D -> Prop): representableP 1 P -> P iO -> (forall d:D, P d -> P (iS d)) -> forall d:D, P d.
  Proof.
  intros [phi [rho Prf]] H0 HS d.
  pose (D_fulfills _ rho (PAeq_induction phi)) as Hind.
  cbn in Prf. cbn in Hind. rewrite Prf.
  apply Hind.
  - rewrite sat_comp. erewrite (@sat_ext _ _ _ _ _ _ (iO .: rho)).
    + rewrite <- Prf. apply H0.
    + now intros [|n].
  - intros d' IH. rewrite sat_comp. erewrite (@sat_ext _ _ _ _ _ _ (iS d' .: rho)).
    + rewrite <- Prf. apply HS. rewrite Prf. apply IH.
    + now intros [|n].
  Qed.
  
  Lemma discriminate (x:D) : x i= iO \/ exists y, x i= iS y.
  Proof.
  generalize x. apply PA_induction.
  - represent.
  - left. apply ieq_refl.
  - intros d IH. right.
    exists d. apply ieq_refl.
  Qed.

  Lemma add_succ_l : forall a b, (iS a) i⊕ b i= iS (a i⊕ b).
  Proof.
  specialize (D_fulfills ax_add_rec emptyEnv). cbn in D_fulfills.
  intros a b. apply D_fulfills.
  apply (PAeq_FA ax_add_rec). do 7 right. now left.
  Qed.

  Lemma add_zero_l b :  iO i⊕ b i= b.
  Proof.
  specialize (D_fulfills ax_add_zero emptyEnv). cbn in D_fulfills.
  apply D_fulfills.
  apply (PAeq_FA). do 6 right. now left.
  Qed.

  Lemma add_zero_r a : a i⊕ iO i= a.
  Proof.
  elim a using PA_induction.
  - represent.
  - apply add_zero_l.
  - intros d IH. 
    pose proof (add_succ_l d iO) as Hsl.
    eapply ieq_trans. 1:exact Hsl.
    apply ieq_congr_succ, IH.
  Qed. 

  Lemma add_succ_r a b : a i⊕ (iS b) i= iS (a i⊕ b).
  Proof.
  elim a using PA_induction.
  - represent.
  - eapply ieq_trans. 1:apply (add_zero_l (iS b)). apply ieq_congr_succ, ieq_sym, add_zero_l.
  - intros d IH.
    eapply ieq_trans. 1:apply (add_succ_l d (iS b)). apply ieq_congr_succ. eapply ieq_trans. 
    + apply IH.
    + apply ieq_sym, add_succ_l.
  Qed.

  Lemma add_comm a b : a i⊕ b i= b i⊕ a.
  Proof.
  elim a using PA_induction.
  - represent.
  - eapply ieq_trans.
    + apply (add_zero_l b).
    + apply ieq_sym, (add_zero_r b).
  - intros a' IH.
    eapply ieq_trans. 2:eapply ieq_trans.
    + apply (add_succ_l a' b).
    + apply ieq_congr_succ, IH.
    + apply ieq_sym, add_succ_r.
  Qed.

  Lemma add_assoc a b c : a i⊕ (b i⊕ c) i= (a i⊕ b) i⊕ c.
  Proof. 
  elim a using PA_induction.
  - represent.
  - eapply ieq_trans.
    + apply add_zero_l.
    + apply ieq_congr_add. 1: apply ieq_sym, add_zero_l. apply ieq_refl.
  - intros a' IH.
    eapply ieq_trans. 2:eapply ieq_trans. 3:eapply ieq_trans.
    + apply (add_succ_l).
    + apply ieq_congr_succ, IH.
    + apply ieq_sym, add_succ_l.
    + apply ieq_congr_add. 2:apply ieq_refl. apply ieq_sym, add_succ_l.
  Qed.

  Lemma mul_zero_l a : iO i⊗ a i= iO.
  Proof. apply (D_fulfills ax_mult_zero (fun _ => iO)). apply PAeq_FA. do 8 right. now left. Qed.

  Lemma mul_succ_l a b : iS a i⊗ b i= b i⊕ a i⊗ b.
  Proof. apply (D_fulfills ax_mult_rec (fun _ => iO)). apply PAeq_FA. do 9 right. now left. Qed.

  Lemma mul_zero_r a : a i⊗ iO i= iO.
  Proof.
  elim a using PA_induction.
  - represent.
  - apply mul_zero_l.
  - intros d IH. eapply ieq_trans. 2: eapply ieq_trans.
    + apply mul_succ_l.
    + apply add_zero_l.
    + apply IH.
  Qed.

  Lemma mul_succ_r a b : a i⊗ iS b i= a i⊕ a i⊗ b.
  Proof.
  elim a using PA_induction.
  - represent. 
  - eapply ieq_trans. 2: eapply ieq_trans.
    + apply mul_zero_l.
    + apply ieq_sym, add_zero_l.
    + apply ieq_congr_add. 1: apply ieq_refl. apply ieq_sym, mul_zero_l.
  - intros d IH. 
    eapply ieq_trans. 1: apply mul_succ_l.
    eapply ieq_trans. 1: apply ieq_congr_add; [apply ieq_refl | apply IH].
    eapply ieq_trans. 1: apply add_assoc.
    eapply ieq_trans. 1: apply ieq_congr_add; [apply add_succ_l | apply ieq_refl].
    eapply ieq_trans. 1: apply ieq_congr_add; [apply ieq_congr_succ | apply ieq_refl]; apply add_comm. 
    eapply ieq_trans. 1: apply ieq_congr_add; [apply ieq_sym, add_succ_l | apply ieq_refl].
    eapply ieq_trans. 1: apply ieq_sym, add_assoc.
    eapply ieq_congr_add. 1: apply ieq_refl.
    apply ieq_sym, mul_succ_l.
  Qed.

  Lemma mul_comm a b : a i⊗ b i= b i⊗ a.
  Proof.
  elim a using PA_induction.
  - represent.
  - eapply ieq_trans.
    + apply (mul_zero_l b).
    + apply ieq_sym, (mul_zero_r b).
  - intros a' IH.
    eapply ieq_trans. 2:eapply ieq_trans.
    + apply (mul_succ_l a' b).
    + apply ieq_congr_add; [apply ieq_refl | apply IH].
    + apply ieq_sym, mul_succ_r.
  Qed.

  Definition proj1 {X:Type} {Y:X->Type} (H:{x:X&Y x}) : X := match H with existT x y => x end.

  Lemma example (a b : D) : representableP 0 (a i⊕ b i= b i⊕ a).
  Proof. Time represent. Show Proof. Defined. (* Not opaque, so we can pull out the representative witness later *)

  Eval cbn in (proj1 (example iO iO)).

  Lemma only_logic : representableP 0 (~(True <-> False)).
  Proof. represent. Defined.

  Lemma large : representableP 0 
    (True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    \/ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    \/ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True).
  Proof. Time representNP. Restart. Time represent. Defined. 



End ReificationExample.
