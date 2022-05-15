Require Import Vector.
From Undecidability.FOL.Basics Require Import Syntax.Facts.
From Undecidability.FOL.Basics.Semantics.Tarski Require Import FullFacts FragmentFacts.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.Synthetic Require Import Definitions.

Set Default Proof Using "Type".
Set Default Goal Selector "!".
Set Mangle Names.
Inductive syms_func : Type := .
(** Double negation translation. Valid for e.g. FSAT *)
Section translation. 
  Import FragmentSyntax.
  Existing Instance FragmentSyntax.frag_operators.
  Existing Instance falsity_on.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}. 

  Notation "phi '-->' psi" := (@bin _ _ frag_operators falsity_on Impl phi psi) (at level 43, right associativity).
  

  (** We try to be clever and translate using as few unnecessary negations as possible *)
  Fixpoint translate_form {f:falsity_flag} (phi : (@form _ _ full_operators f)) {struct phi} : 
    (@form _ _ FragmentSyntax.frag_operators falsity_on) := 
  match phi with 
  | falsity => falsity
  | atom P v => atom P v
  | bin Conj phi1 phi2 => conj_to_impl_chain phi1 (conj_to_impl_chain phi2 falsity) --> falsity
  | bin Disj phi1 phi2 => disj_to_impl_chain phi1 (disj_to_impl_chain phi2 falsity)
  | bin FullSyntax.Impl phi1 phi2 => conj_to_impl_chain phi1 (translate_form phi2)
  | quant FullSyntax.All phi => @quant _ _ _ falsity_on All (translate_form phi)
  | quant Ex phi => (@quant _ _ _ falsity_on All (translate_negated phi)) --> falsity
  end
  with translate_negated {f:falsity_flag} (phi : (@form _ _ full_operators f)) {struct phi} : 
    (@form _ _ FragmentSyntax.frag_operators falsity_on) := 
  match phi with 
  | falsity => falsity --> falsity
  | atom P v => atom P v --> falsity
  | bin Conj phi1 phi2 => conj_to_impl_chain phi1 (conj_to_impl_chain phi2 falsity)
  | bin Disj phi1 phi2 => disj_to_impl_chain phi1 (disj_to_impl_chain phi2 falsity) --> falsity
  | bin FullSyntax.Impl phi1 phi2 => (conj_to_impl_chain phi1 (translate_form phi2)) --> falsity
  | quant Ex phi => @quant _ _ _ falsity_on All (translate_negated phi)
  | quant FullSyntax.All phi => (@quant _ _ _ falsity_on All (translate_form phi)) --> falsity
  end
  with conj_to_impl_chain {f:falsity_flag} (phi : (@form _ _ full_operators f)) 
              (terminal : (@form _ _ FragmentSyntax.frag_operators falsity_on)) {struct phi} : 
    (@form _ _ FragmentSyntax.frag_operators falsity_on) := 
  match phi with 
  | falsity => falsity --> terminal
  | atom P v => atom P v --> terminal
  | bin Conj phi1 phi2 => conj_to_impl_chain phi1 (conj_to_impl_chain phi2 terminal)
  | bin Disj phi1 phi2 => (disj_to_impl_chain phi1 (disj_to_impl_chain phi2 falsity)) --> terminal
  | bin FullSyntax.Impl phi1 phi2 => conj_to_impl_chain phi1 (translate_form phi2) --> terminal
  | quant FullSyntax.All phi => @quant _ _ _ falsity_on All (translate_form phi) --> terminal
  | quant Ex phi => ((@quant _ _ _ falsity_on All (translate_negated phi)) --> falsity) --> terminal
  end
  with disj_to_impl_chain {f:falsity_flag} (phi : (@form _ _ full_operators f)) 
              (terminal : (@form _ _ FragmentSyntax.frag_operators falsity_on)) {struct phi} : 
    (@form _ _ FragmentSyntax.frag_operators falsity_on) := 
  match phi with 
  | falsity => (falsity --> falsity) --> terminal
  | atom P v => (atom P v --> falsity) --> terminal
  | bin Conj phi1 phi2 => (conj_to_impl_chain phi1 (conj_to_impl_chain phi2 falsity)) --> terminal
  | bin Disj phi1 phi2 => disj_to_impl_chain phi1 (disj_to_impl_chain phi2 terminal)
  | bin FullSyntax.Impl phi1 phi2 => ((conj_to_impl_chain phi1 (translate_form phi2)) --> falsity) --> terminal
  | quant Ex phi => (@quant _ _ _ falsity_on All (translate_negated phi)) --> terminal
  | quant FullSyntax.All phi => ((@quant _ _ _ falsity_on All (translate_form phi)) --> falsity) --> terminal
  end.
  
  Context {D:Type}.
  Context {I : interp D}.

  (** Define interpretations for full and frag syntax, which are equivalent. *)
  Definition tarski_full_tarski_interp (II:interp D) : FullCore.interp D.
  Proof.
  destruct II; split; easy.
  Defined.

  Definition full_tarski_tarski_interp (II:FullCore.interp D) : interp D.
  Proof.
  destruct II; split; easy.
  Defined.

  Definition full_interp_inverse_1 II : tarski_full_tarski_interp (full_tarski_tarski_interp II) = II.
  Proof. now destruct II. Qed.

  Definition full_interp_inverse_2 II : full_tarski_tarski_interp (tarski_full_tarski_interp II) = II.
  Proof. now destruct II. Qed.

  Notation "rho ⊨ phi" := (@sat _ _ D I falsity_on rho phi).
  Notation "rho 'f⊨' phi" := (@FullCore.sat _ _ D (tarski_full_tarski_interp I) _ rho phi) (at level 20).

  (** Terms are evaluated to equal results *)
  Lemma eval_same env trm : eval env trm = @FullCore.eval _ _ D (tarski_full_tarski_interp I) env trm.
  Proof.
  induction trm as [n|k v IH].
  - easy.
  - destruct I. cbn. erewrite VectorSpec.map_ext_in. 1:reflexivity.
    apply IH.
  Qed.

  Lemma eval_same_atom t (vt:Vector.t D (ar_preds t)) : i_atom vt <-> @FullCore.i_atom _ _ D (tarski_full_tarski_interp I) t vt.
  Proof.
  destruct I. cbn. easy.
  Qed.

  Context {Ddec : forall {f:falsity_flag} phi (rho:env D), dec (rho f⊨ phi)}.

  Lemma equiv_impl X Y (P:Prop) : X <-> Y -> (X -> P) <-> (Y -> P).
  Proof.
  intros H. rewrite H. easy.
  Qed.

  Ltac recsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [idtac|f nn] end in f n.

  (** Show correctness by induction. *)
  Lemma correct (f:falsity_flag) rho (phi : (@form _ _ full_operators f)) : 
     (rho ⊨ translate_form phi <-> rho f⊨ phi)
  /\ (rho ⊨ translate_negated phi <-> ~ (rho f⊨ phi))
  /\ (forall P wterm, (rho ⊨ wterm <-> P) -> rho ⊨ conj_to_impl_chain phi wterm <-> ((rho f⊨ phi) -> P))
  /\ (forall P wterm, (rho ⊨ wterm <-> P) -> rho ⊨ disj_to_impl_chain phi wterm <-> (~(rho f⊨ phi) -> P)).
  Proof using Ddec.
  induction phi as [|p v|f [| |] l IHl r IHr|f [|] s IHs] in rho|-*.
  - cbn. recsplit 3. 1-2:easy. 1-2:intros term wterm ->; tauto.
  - recsplit 3.
    + cbn. erewrite (Vector.map_ext). 1: apply eval_same_atom. apply eval_same.
    + cbn. erewrite (Vector.map_ext). 1: apply equiv_impl; apply eval_same_atom. apply eval_same.
    + intros term wterm H. cbn. rewrite <- eval_same_atom. rewrite <- H. erewrite (Vector.map_ext). 1:easy.  apply eval_same. 
    + intros term wterm H. cbn. rewrite H. apply equiv_impl, equiv_impl. erewrite (Vector.map_ext). 1:apply eval_same_atom. apply eval_same.
  - destruct (IHl rho) as [l1 [l2 [l3 l4]]], (IHr rho) as [r1 [r2 [r3 r4]]]. recsplit 3.
    + cbn. rewrite l3. 2:easy. rewrite r3. 2:easy. split.
      * intros H. destruct (Ddec l rho) as [Hl|Hnl], (Ddec r rho) as [Hr|Hnr]. 1:easy. all:exfalso; apply H; intros Hcl Hcr; cbn; easy.
      * intros [Hl Hr] H. now apply H.
    + cbn. rewrite l3. 2:easy. rewrite r3. 2:easy. tauto.
    + intros term wterm H. cbn. rewrite l3. 2:easy. rewrite r3. 2:easy. rewrite H. tauto.
    + intros term wterm H. cbn. rewrite l3. 2:easy. rewrite r3. 2:easy. rewrite H. apply equiv_impl. tauto.
  - destruct (IHl rho) as [l1 [l2 [l3 l4]]], (IHr rho) as [r1 [r2 [r3 r4]]]. 
    cbn. recsplit 3.
    + rewrite l4. 2:easy. rewrite r4. 2:easy.  split.
      * intros H. destruct (Ddec l rho) as [Hl|Hnl], (Ddec r rho) as [Hr|Hnr]. 1-3:tauto.
        exfalso. now apply H.
      * tauto.
    + rewrite l4. 2:easy. rewrite r4. 2:easy. tauto.
    + intros term wterm H. rewrite l4. 2:easy. rewrite r4. 2:easy. rewrite H. apply equiv_impl. split. 2:tauto.
      intros Hc. destruct (Ddec l rho) as [Hl|Hnl], (Ddec r rho) as [Hr|Hnr]. 1-3:tauto. exfalso. now apply Hc.
    + intros term wtertranslate_formm H. rewrite l4. 2:easy. rewrite r4. 2:easy. rewrite H. tauto.
  - destruct (IHl rho) as [l1 [l2 [l3 l4]]], (IHr rho) as [r1 [r2 [r3 r4]]].
    cbn. rewrite l3. 2:easy. rewrite r1. recsplit 3.
    + tauto.
    + tauto.
    + intros term wterm H. rewrite l3. 2:easy. rewrite H. rewrite r1. tauto.
    + intros term wterm H. rewrite l3. 2:easy. rewrite H. rewrite r1. tauto.
  - cbn. recsplit 3.
    + split.  
      * intros H d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH1. apply H.
      * intros H d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite IH1. apply H.
    + split. 
      * intros Hc H. apply Hc. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite IH1. apply H.
      * intros Hc H. apply Hc. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH1. apply H.
    + intros term wterm ->. split.
      * intros Hc H. apply Hc. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite IH1. apply H.
      * intros Hc H. apply Hc. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH1. apply H.
    + intros term wterm ->. split.
      * intros Hc H. apply Hc. intros Hcc. apply H. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH1. apply Hcc.
      * intros Hc H. apply Hc. intros Hcc. apply H. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite IH1. apply Hcc.
  - cbn. recsplit 3.
    + split.
      * intros H. destruct (Ddec (∃ s) rho) as [[e He]|Hne].
        -- now exists e.
        -- exfalso. apply H. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]].
           rewrite IH2. intros Hc. apply Hne. now exists d.
      * intros [d Hd] Hc. contradict Hd. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH2. apply Hc.
    + split.
      * intros Hc [d Hd]. contradict Hd.  destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH2. apply Hc.
      * intros Hc d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite IH2. intros H. apply Hc. now exists d.
    + intros term wterm ->. apply equiv_impl. split.
      * intros H. destruct (Ddec (∃ s) rho) as [[e He]|Hne].
        -- now exists e.
        -- exfalso. apply H. intros d. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]].
           rewrite IH2. intros Hc. apply Hne. now exists d.
      * intros [d Hd] Hc. contradict Hd. destruct (IHs (d.:rho)) as [IH1 [IH2 [IH3 IH4]]]. rewrite <- IH2. apply Hc.
    + intros term wterm ->. apply equiv_impl. firstorder.
  Qed.
End translation.


