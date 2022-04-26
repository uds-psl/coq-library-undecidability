From Undecidability.FOL Require Import Syntax PA.
Import FullSyntax.
From Undecidability.FOL Require Import FullTarski FullTarski_facts.
Require Import Undecidability.FOL.Reification.GeneralReflection.
From Undecidability.FOL Require Import Hoas.
Import Vector.VectorNotations.
Require Import String Vector List.

Section Reification.
  (* We assume an arbitrary model of PA which fulfills the axioms of PA *)

  #[local]
  Existing Instance PA_funcs_signature.
  #[local]
  Existing Instance PA_preds_signature.

  Context (D':Type).
  Context {I' : interp D'}.
  Instance I : interp D'.
  Proof. split; intros k; destruct k; intros v. 
  - exact (i_func v).
  - exact (i_func v).
  - exact (i_func v).
  - exact (i_func v).
  - inversion v. inversion X. exact (h = h0).
  Defined.
  Context {D_fulfills : forall f rho, PAeq f -> rho ⊨ f}.

  Notation "'iO'" := (@i_func PA_funcs_signature PA_preds_signature D' _ Zero ([])) (at level 1) : PA_Notation.
  Notation "'iS' x" := (@i_func PA_funcs_signature PA_preds_signature D' _ Succ ([x])) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D' _ Plus ([x ; y]) ) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D' _ Mult ([x ; y]) ) (at level 38) : PA_Notation.
  Notation "x 'i=' y" := (@i_atom PA_funcs_signature PA_preds_signature D' _ Eq ([x ; y]) ) (at level 40) : PA_Notation.
  Notation "x '⊕' y" := (bFunc Plus ([x; y])) (at level 39) : hoas_scope.
  Notation "x '==' y" := (bAtom Eq ([x; y])) (at level 40) : hoas_scope.
  Open Scope string_scope.

  Instance PA_reflector : tarski_reflector := buildDefaultTarski 
                        (iO) (* we need a point in D *)
                        (anyVariableOf ("D'" :: nil)). (* We need to know when some type is D *)

  Definition emptyEnv := emptyEnv.



















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
  Lemma PA_induction (P:D' -> Prop): representableP 1 P -> P iO -> (forall d:D', P d -> P (iS d)) -> forall d:D', P d.
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

  Lemma add_succ_l : forall a b, (iS a) i⊕ b i= iS (a i⊕ b).
  Proof.
  specialize (D_fulfills ax_add_rec emptyEnv). cbn -[I] in D_fulfills.
  intros a b. apply D_fulfills.
  apply (PAeq_FA ax_add_rec). do 7 right. now left.
  Qed.

  Lemma add_zero_l b :  iO i⊕ b i= b.
  Proof.
  specialize (D_fulfills ax_add_zero emptyEnv). cbn -[I] in D_fulfills.
  apply D_fulfills.
  apply (PAeq_FA). do 6 right. now left.
  Qed.

  Lemma add_zero_r a : a i⊕ iO i= a.
  Proof.
  elim a using PA_induction.
  - now exists ($0 ⊕ zero == $0), (fun _ => iO).  - apply add_zero_l.
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

























































  Section ReflectionExtension.
    Import List.ListNotations.
    Import MetaCoq.Template.Ast MetaCoq.Template.TemplateMonad.Core.
    Import Undecidability.FOL.Reification.GeneralReflection.
    Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : Syntax.term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP _ _ 0 (t1==t2) rho (d1 = d2).
    Proof. intros pt1 pt2. cbn. unfold representsF in pt1, pt2. cbn in pt1, pt2. rewrite pt1, pt2. easy. (*now rewrite D_ext.*)
    Defined.
    MetaCoq Quote Definition qMergeFormEq := (constructForm Eq).
    MetaCoq Quote Definition qMergeEqProp := mergeEqProp.


    Definition reifyCoqEq : baseConnectiveReifier := fun tct qff l fuel envTerm env fPR fTR => match l with (tv::x::y::nil) => if maybeD tct tv then
                                               xr <- fTR tct qff x envTerm env ;;
                                               yr <- fTR tct qff y envTerm env ;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                               ret (tApp qMergeFormEq (xt::yt::nil), tApp qMergeEqProp (envTerm::x::y::xt::yt::xp::yp::nil)) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition varsCoqEq : baseConnectiveVars := fun lst fuel tct _ fUVT => match lst with tv::x::y::nil => if maybeD tct tv then
                                               xr <- fUVT x;;
                                               yr <- fUVT y;;
                                               ret (List.app xr yr) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition reifyBLC (s:string) : baseConnectiveReifier := match s with "eq"%string => reifyCoqEq | _ => fun _ _ _ _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition varsBLC (s:string) : baseConnectiveVars := match s with "eq"%string => varsCoqEq | _ => fun _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
  End ReflectionExtension.
  Instance PA_reflector_ext : tarski_reflector_extensions PA_reflector := {| (*Cannot define instance in section because they are dropped afterwards *)
    baseLogicConnHelper := Some (reifyBLC);
    baseLogicVarHelper := Some (varsBLC);
    termReifierVarHelper := None;
    termReifierReifyHelper := None;
    formReifierVarHelper := None;
    formReifierReifyHelper := None
  |}.

Existing Instance I' | 0.

  Lemma add_succ_l_ext : forall a b, (iS a) i⊕ b = iS (a i⊕ b).
  Proof.
  specialize (D_fulfills ax_add_rec emptyEnv). cbn -[I] in D_fulfills.
  intros a b. cbn. apply D_fulfills.
  apply (PAeq_FA ax_add_rec). do 7 right. now left.
  Qed.

  Lemma add_zero_l_ext b : iO i⊕ b = b.
  Proof.
  specialize (D_fulfills ax_add_zero emptyEnv). cbn -[I] in D_fulfills.          
  cbn. apply D_fulfills.
  apply (PAeq_FA). do 6 right. now left.
  Qed.

  Lemma add_zero_r_ext a : a i⊕ iO = a.
  Proof.
  elim a using PA_induction.
  - represent.
  - apply add_zero_l.
  - intros d IH. cbn.
    now rewrite add_succ_l_ext, IH.
  Qed. 

  Lemma add_succ_r_ext a b : a i⊕ (iS b) = iS (a i⊕ b).
  Proof.
  elim a using PA_induction.
  - represent.
  - now rewrite add_zero_l_ext, add_zero_l_ext.
  - intros d IH. cbn.
    now rewrite add_succ_l_ext, IH, <- add_succ_l_ext.
  Qed.

Existing Instance I | 0.





















  Lemma add_comm_ext e : e ⊨  << ∀' a b, a ⊕ b == b ⊕ a.
  Proof.
  cbn. intros a b.
  elim a using PA_induction.
  - represent.
    (* unfold representableP. unfold representsP.
    exists (<< Free b a, a ⊕ b == b ⊕ a). (* Order is important ! *)
    exists (fun v => if Nat.eqb v 0 then b else iO).
    intros d. cbn. reflexivity. *)
  - now rewrite add_zero_l_ext, add_zero_r_ext.
  - intros a' IH. cbn.
    now rewrite add_succ_l_ext, IH, <- add_succ_r_ext.
  Qed.













