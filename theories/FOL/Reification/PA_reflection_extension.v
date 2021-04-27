Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import Undecidability.FOL.Reification.GeneralReflection.
Require Import Undecidability.FOL.PA.
Import MetaCoq.Template.Ast MetaCoq.Template.TemplateMonad.Core.
Import Vector.VectorNotations.
Require Import String List.



Fixpoint num n := match n with 0 => zero | S n => σ (num n) end.

Section ReificationExample.
  (* We assume an arbitrary model of PA which fulfills the axioms of PA *)
  Context (D':Type).
  Context {I : interp D'}.
  Context {D_ext : extensional I}. (* Furthermore, we assume that a i= b -> a = b, i.e. equality is extensional*)
  Context {D_fulfills : forall f rho, PAeq f -> rho ⊨ f}.

  Notation "'iO'" := (@i_func _ _ D' I Zero ([])) (at level 1) : PA_Notation.
  Notation "'iS' x" := (@i_func _ _ D' I Succ ([x])) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (@i_func _ _ D' I Plus ([x ; y]) ) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (@i_func _ _ D' I Mult ([x ; y]) ) (at level 38) : PA_Notation.
  Notation "x 'i=' y" := (@i_atom _ _ D' I Eq ([x ; y]) ) (at level 40) : PA_Notation.
  Open Scope string_scope.



  Fixpoint inum n := match n with 0 => iO | S n => iS (inum n) end.

  Instance PA_reflector : tarski_reflector := buildDefaultTarski 
                        (iO) (* we need a point in D *)
                        (anyVariableOf ("D'" :: nil)). (* We need to know when some type is D *)


  Section ReflectionExtension.
    (* Do a correctness proof for the specific extension *)
    Definition mergeNum (rho:nat -> D) (n:nat) : representsF (inum n) (num n) rho.
    Proof. unfold representsF. induction n.
    * easy.
    * cbn. do 2 f_equal. cbn in IHn. now rewrite IHn.
    Defined.
    (* Define some MetaCoq terms we will need later *)
    MetaCoq Quote Definition qNum := inum.
    MetaCoq Quote Definition qMergeNum := mergeNum.
    MetaCoq Quote Definition qMergeTermNum := @num.

    Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : Syntax.term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP _ _ 0 (t1==t2) rho (d1 = d2).
    Proof. intros pt1 pt2. cbn. unfold representsF in pt1, pt2. cbn in pt1, pt2. rewrite pt1, pt2. now rewrite D_ext.
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
    Definition findVarsTerm : termFinderVars := fun fuel t fUVT => match t with (tApp qMu (k::nil)) => ret nil | _ => fail "Fail" end.
    Definition reifyTerm : termFinderReifier := fun tct qff fuel t envTerm env fTR => match t with tApp qMu (k::nil) => ret (tApp qMergeTermNum (k::nil), tApp qMergeNum (envTerm::k::nil)) | _ => fail "Fail" end.
  End ReflectionExtension.
  (* If we want to extend the capabilities, we define an extension point instance *)
  Instance PA_reflector_ext : tarski_reflector_extensions PA_reflector := {| (*Cannot define instance in section because they are dropped afterwards *)
    baseLogicConnHelper := Some (reifyBLC);
    baseLogicVarHelper := Some (varsBLC);
    termReifierVarHelper := Some (findVarsTerm);
    termReifierReifyHelper := Some (reifyTerm);
    formReifierVarHelper := None;
    formReifierReifyHelper := None
  |}.
  (* We can now use = in our terms, and automatically find the proper representative. This also works for num *)

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
  
  Lemma disciminate (x:D) : x = iO \/ exists y, x = iS y.
  Proof.
  generalize x. apply PA_induction.
  - represent.
  - now left.
  - intros d [IH|IH]; right.
    + exists iO. now rewrite IH.
    + now exists d.
  Qed.

  Lemma add_succ_l a b : (iS a) i⊕ b = iS (a i⊕ b).
  Proof.
  rewrite <- D_ext.
  specialize (D_fulfills ax_add_rec emptyEnv). cbn in D_fulfills.
  apply D_fulfills.
  apply (PAeq_FA ax_add_rec). do 7 right. now left.
  Qed.

  Lemma add_zero_l b : iO i⊕ b = b.
  Proof.
  rewrite <- D_ext.
  specialize (D_fulfills ax_add_zero emptyEnv). cbn in D_fulfills.
  apply D_fulfills.
  apply (PAeq_FA). do 6 right. now left.
  Qed.

  Lemma add_zero_r a : a i⊕ iO = a.
  Proof.
  elim a using PA_induction.
  - represent.
  - apply add_zero_l.
  - intros d IH. 
    rewrite add_succ_l. now rewrite IH.
  Qed. 

  Lemma add_succ_r a b : a i⊕ (iS b) = iS (a i⊕ b).
  Proof.
  elim a using PA_induction.
  - represent.
  - now rewrite ! add_zero_l.
  - intros d IH. now rewrite ! add_succ_l, IH.
  Qed.

  Lemma add_comm a b : a i⊕ b = b i⊕ a.
  Proof.
  elim a using PA_induction.
  - represent.
  - now rewrite add_zero_l, add_zero_r.
  - intros a' IH. now rewrite add_succ_l, add_succ_r.
  Qed.

  Lemma add_assoc a b c : a i⊕ (b i⊕ c) = (a i⊕ b) i⊕ c.
  Proof.
  elim a using PA_induction.
  - represent.
  - now rewrite ! add_zero_l. 
  - intros a' IH.
    now rewrite ! add_succ_l, IH.
  Qed.

  Lemma mul_zero_l a : iO i⊗ a = iO.
  Proof.
  rewrite <- D_ext.
  apply (D_fulfills ax_mult_zero (fun _ => iO)). apply PAeq_FA. do 8 right. now left.
  Qed.

  Lemma mul_succ_l a b : iS a i⊗ b = b i⊕ a i⊗ b.
  Proof.
  rewrite <- D_ext.
  apply (D_fulfills ax_mult_rec (fun _ => iO)). apply PAeq_FA. do 9 right. now left.
  Qed.

  Lemma mul_zero_r a : a i⊗ iO = iO.
  Proof.
  elim a using PA_induction.
  - represent.
  - apply mul_zero_l.
  - intros d IH. now rewrite mul_succ_l, add_zero_l, IH.
  Qed.

  Lemma mul_succ_r a b : a i⊗ iS b = a i⊕ a i⊗ b.
  Proof.
  elim a using PA_induction.
  - represent. 
  - now rewrite ! mul_zero_l, add_zero_l.
  - intros d IH.
    rewrite ! mul_succ_l, ! add_succ_l. do 2 f_equal.
    rewrite IH. rewrite ! add_assoc.
    now rewrite (add_comm b d).
  Qed.

  Lemma mul_comm a b : a i⊗ b = b i⊗ a.
  Proof.
  elim a using PA_induction.
  - represent.
  - now rewrite mul_zero_l, mul_zero_r.
  - intros a' IH. now rewrite mul_succ_l, mul_succ_r.
  Qed.

  Definition test : representableP 0 (inum 5 = iS (iS (iS (iS (iS iO))))).
  Proof. represent. Defined.
  Definition proj1 {X:Type} {Y:X->Type} (H:{x:X&Y x}) : X := match H with existT x y => x end.
  Eval cbn in (proj1 test).

End ReificationExample.
