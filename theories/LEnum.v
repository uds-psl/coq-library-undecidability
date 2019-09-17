(** * Nla  *)

From Undecidability.L Require Import Eval.
From Undecidability.FOLC Require Import Extend FOL.

From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode Datatypes.Lists Reductions.H10_to_L Datatypes.LNat Datatypes.LOptions.

Inductive term' := var_term' : nat -> term' | Func' (name : nat) | App' : term' -> term' -> term'. 

Inductive varornot := isvar | novar.
Inductive wf : varornot -> term' -> Prop :=
| wf_var n : wf isvar (var_term' n) 
| wf_fun f : wf novar (Func' f) 
| wf_app v s t : wf v s -> wf novar t -> wf novar (App' s t).

Instance max : Signature.
Proof.
  unshelve econstructor.
  - exact (nat * nat)%type.
  - exact (nat * nat)%type.
  - exact snd.
  - exact snd.
Defined.

Fixpoint to_term (a : list (@term max)) (t : term')  :=
  match t with
  | var_term' n => var_term n
  | Func' n => Func (n, |List.rev a|) (of_list (List.rev a))
  | App' s t => to_term (to_term List.nil s :: a) t
  end.

Definition mkApps n l (L : Vector.t _ n) := fold_right App' L l.

Fixpoint of_term (t : @term max) :=
  match t with
  | var_term n => var_term' n
  | Func (n, m) l => mkApps (Func' n) (map of_term l) 
  end.

Require Import Equations.Prop.DepElim.

Lemma Func_cast F n n' (ts : Vector.t _ n) (ts' : Vector.t _ n') :
  forall (H : n = n'), cast ts H = ts' -> Func (F, n) ts = Func (F, n') ts'.
Proof.
  intros -> H. f_equal. revert H.
  dependent induction ts; cbn; congruence.
Qed.

Lemma Pred_cast P n n' (ts : Vector.t _ n) (ts' : Vector.t _ n') :
  forall (H : n = n'), cast ts H = ts' -> Pred (P, n) ts = Pred (P, n') ts'.
Proof.
  intros -> H. f_equal. revert H.
  dependent induction ts; cbn; congruence.
Qed.

Lemma cast_nil X n (v : Vector.t X n) H :
  cast v H = append v VectorDef.nil.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma cast_app X n (v : Vector.t X n) (A B : list X) H :
  cast (append (of_list (A ++ B)) v) H = append (of_list A) (append (of_list B) v).
Proof.
  induction A in B, H |- *; cbn.
  - apply cast_eq.
  - now rewrite IHA.
Qed.

Lemma to_term_mkApps n k (v : Vector.t term k) A :
  (forall s, vec_in s v -> to_term ([]) (of_term s) = s) 
   -> to_term A (mkApps (Func' n) (map of_term v))
     = Func (n, List.length (List.rev A) + k) (append (of_list (List.rev A)) v).
Proof.
  induction v in A |- *; cbn; intros H.
  - assert (Heq : | List.rev A | = (| List.rev A |) + 0) by lia.
    eapply Func_cast with (H:=Heq). apply cast_nil.
  - rewrite IHv; eauto. rewrite H; eauto. cbn.
    assert (Heq : (| List.rev A ++ ([h]) |) + n0 = (|List.rev A |) + S n0).
    { rewrite app_length. cbn. lia. }
    eapply Func_cast with (H:=Heq). now rewrite cast_app.
Qed.

Lemma to_term_of_term t :
  to_term List.nil (of_term t) = t.
Proof.
  induction t using strong_term_ind; cbn; trivial.
  destruct F. now apply to_term_mkApps.
Qed.

Inductive form' := Fal' | Pred' (P : nat) (args : list term') | Impl' (phi1 phi2 : form') | All' (phi : form').

Fixpoint to_form (f : form') :=
  match f with
  | Fal' => Fal
  | Pred' P L => Pred (P, _) (of_list (List.map (to_term List.nil) L))
  | Impl' phi1 phi2 => Impl (to_form phi1) (to_form phi2)
  | All' phi => All (to_form phi)
  end.

Fixpoint of_form (f : form) :=
  match f with
  | Fal => Fal'
  | Pred (P,_) L => Pred' P (to_list (map of_term L))
  | Impl phi1 phi2 => Impl' (of_form phi1) (of_form phi2)
  | All phi => All' (of_form phi)
  end.

Lemma to_list_length X n (v : Vector.t X n) :
  length (to_list v) = n.
Proof.
  unfold to_list. induction v; cbn; congruence.
Qed.

Lemma to_form_of_form f :
  to_form (of_form f) = f.
Proof.
  induction f; cbn; try congruence.
  destruct P. cbn. assert (Heq : | [to_term ([]) p | p ∈ to_list (map of_term t)] | = n0).
  { rewrite map_length. apply to_list_length. }
  eapply Pred_cast with (H:=Heq). revert Heq. dependent induction t; trivial.
  intros H. cbn. f_equal; try apply IHt. apply to_term_of_term.
Qed.

Run TemplateProgram (tmGenEncode "enc_term'" term').
Hint Resolve enc_term'_correct : Lrewrite.

Instance term_var_term': computable var_term'. extract constructor. Qed.
Instance term_Func' : computable Func'.  extract constructor. Qed.
Instance term_App' : computable App'.  extract constructor. Qed.

Definition App'' '(s,t) := App' t s.
Instance term_App'' : computable App''. extract. Qed.

Fixpoint L_term' n :=
  match n with
  | 0 => []
  | S n => L_term' n ++
          List.map var_term' (L_nat n) ++
          List.map Func' (L_nat n) ++
          List.map App'' (list_prod (L_term' n) (L_term' n))
  end.
          
Instance enum_term' : enumT term'.
Proof.
  exists L_term'.
  - eauto.
  - intros t. induction t.
    + destruct (el_T n) as [m].
      exists (1 + m). cbn. in_app 2. eauto.
    + destruct (el_T name) as [m].
      exists (1 + m). cbn. in_app 3. eauto.
    + destruct IHt1 as [m1]. destruct IHt2 as [m2].
      exists (1 + m1 + m2). cbn. in_app 4. in_collect (t2, t1); eapply cum_ge'; eauto; omega.
Defined.

Instance term_L_term' : computable L_term'. extract. Qed.

Fixpoint L_wf v n :=
  match n with
  | 0 => []
  | S n => L_wf v n ++
               match v with
               | isvar => List.map var_term' (L_nat n)
               | novar => List.map Func' (L_nat n) ++
                         List.map App'' (list_prod (L_wf novar n) (L_wf novar n)) ++
                         List.map App'' (list_prod (L_wf novar n) (L_wf isvar n))         
               end
  end.

Run TemplateProgram (tmGenEncode "enc_varornot" varornot).
Hint Resolve enc_varornot_correct : Lrewrite.

Instance term_L_wf : computable L_wf.
Proof.
  extract. 
Qed.
  
Lemma enum_wf v : enum (wf v) (L_wf v).
Proof with try (eapply cum_ge'; eauto; omega).
  split. eauto.
  intros t. split.
  - induction 1.
    + destruct (el_T n) as [m]. exists (1 + m). cbn. in_app 2. eauto.
    + destruct (el_T f) as [m]. exists (1 + m). cbn. in_app 2. eauto.
    + destruct (IHwf1) as [m1], (IHwf2) as [m2].
      exists (1 + m1 + m2). cbn. destruct v.
      * in_app 4. in_collect (t, s)...
      * in_app 3. in_collect (t, s)...
  - intros [m]. induction m in v, t, H |-*; cbn in *.
    + eauto.
    + inv_collect. destruct v; inv_collect.
      * econstructor.
      * econstructor.
      * econstructor; eauto.
      * econstructor; eauto.
Qed.

Run TemplateProgram (tmGenEncode "enc_form'" form').
Hint Resolve enc_form'_correct : Lrewrite.

(* Instance term_Fal'  : computable Fal'.   extract constructor. Qed. *)
Instance term_Pred' : computable Pred'.  extract constructor. Qed.
Instance term_Impl' : computable Impl'.  extract constructor. Qed.
Instance term_All'  : computable All'.   extract constructor. Qed.

Definition Impl'' '(s,t) := Impl' s t.
Instance term_Impl'' : computable Impl''. extract. Qed.

Definition Pred'' '(s,t) := Pred' s t.
Instance term_Pred'' : computable Pred''. extract. Qed.

Definition cons'' : term' * list term' -> list term' := fun '(n, L) => n :: L.

Instance term_cons'' : computable cons''.
Proof.
  extract.
Qed.

Definition T_list_term' := @T_list term' _.

Instance term_T_list' : computable T_list_term'.
Proof.
  change (computable
    (fix T_list (n : nat) : list (list term') :=
       match n with
       | 0 => [[]]
       | S n0 => (T_list n0 ++ List.map cons'' (L_term' n0 × T_list n0))%list
       end)).
  extract.
Qed.
Fixpoint L_form' n :=
  match n with
  | 0 => [Fal']
  | S n => L_form' n ++
          List.map Pred'' (list_prod (L_nat n) (T_list_term' n)) ++
          List.map Impl'' (list_prod (L_form' n) (L_form' n)) ++
          List.map All' (L_form' n)
  end.

Instance term_L_form' : computable L_form'. extract. Qed.
          
Instance enum_form' : enumT form'.
Proof.
  exists L_form'.
  - eauto.
  - intros t. induction t.
    + exists 0. cbn. eauto.
    + destruct (el_T P) as [m1]. destruct (el_T args) as [m2].
      exists (1 + m1 + m2). cbn. in_app 2.
      in_collect (P, args); eapply cum_ge'; eauto; omega.
    + destruct IHt1 as [m1]. destruct IHt2 as [m2].
      exists (1 + m1 + m2). cbn. in_app 3. in_collect (t1, t2); eapply cum_ge'; eauto; omega.
    + destruct IHt as [m]. 
      exists (1 + m). cbn. in_app 4. eauto.       
Defined.

Fixpoint subst_term'   (sigmaterm : (fin)  -> term' ) (s : term' ) : _ :=
  match s with
  | var_term'  s => sigmaterm s
  | Func' f => Func' f
  | App' s1 s2 => App' (subst_term' sigmaterm s1) (subst_term' sigmaterm s2)
  end.

Fixpoint subst_term'' (b : bool)  (sigmaterm : (fin)  -> term' ) (s : term' ) : _ :=
  match s with
  | var_term'  s => if b then sigmaterm s else Func' s
  | Func' f => Func' f
  | App' s1 s2 => App' (subst_term'' true sigmaterm s1) (subst_term'' false sigmaterm s2)
  end.

Compute (subst_term'' false (fun _ => var_term' 3) (App' (var_term' 0) (var_term' 1))).

Definition up_term_term'   (sigma : (fin)  -> term' ) : _ :=
  (scons) ((var_term') (var_zero)) ((funcomp) (subst_term' ((funcomp) (var_term' ) (shift))) sigma).

Fixpoint subst_form'   (sigmaterm : (fin)  -> term' ) (s : form' ) : _ :=
  match s with
  | Fal'   => Fal'
  | Pred'  P s0 => Pred' P ((List.map (subst_term' sigmaterm)) s0)
  | Impl'  s0 s1 => Impl'  ((subst_form' sigmaterm) s0) ((subst_form' sigmaterm) s1)
  | All'  s0 => All'  ((subst_form' (up_term_term' sigmaterm)) s0)
  end.

Definition form_shift' n := var_term' (S n).

Inductive sprvie : list form' -> option form' -> form' -> Prop :=
| ieContr A phi psi : sprvie A (Some phi) psi -> phi el A -> sprvie A None psi
| ieIR A phi psi : sprvie (phi :: A) None psi -> sprvie A None (Impl' phi psi)
| ieAllR A phi : sprvie (List.map (subst_form' form_shift') A) None phi -> sprvie A None (All' phi)
| ieAbsurd A phi : sprvie A None Fal' -> sprvie A None phi
| ieAx A phi : sprvie A (Some phi) phi
| ieIL A phi psi xi : sprvie A None phi -> sprvie A (Some psi) xi -> sprvie A (Some (Impl' phi psi)) xi
| ieAllL A phi v t psi : wf v t -> sprvie A (Some (subst_form' (t .: var_term') phi)) psi -> sprvie A (Some (All' phi)) psi.
Arguments sprvie _ _.

Hint Constructors sprvie.

Hint Constructors sprv.

Lemma ext_term' sigma tau phi : (forall x, sigma x = tau x) -> subst_term' sigma phi = subst_term' tau phi.
Proof.
  induction phi; cbn; firstorder congruence.
Qed.

Lemma ext_form' sigma tau phi : (forall x, sigma x = tau x) -> subst_form' sigma phi = subst_form' tau phi.
Proof.
  induction phi in sigma, tau |- *; cbn; try firstorder congruence.
  - intros. f_equal. eapply map_ext. intros; now eapply ext_term'.
  - intros. erewrite IHphi1, IHphi2; eauto.
  - intros. erewrite IHphi; eauto. intros []; cbn. reflexivity.
    unfold funcomp. rewrite H. now eapply ext_term'.
Qed.

Require Import Equations.Prop.DepElim.

Lemma subst_term_of_term sigma t :
  subst_term' (sigma >> of_term) (of_term t) = of_term (subst_term sigma t).
Proof.
  revert sigma.
  induction t using strong_term_ind; cbn; intros.
  - reflexivity.
  - destruct F. dependent induction v; cbn.
    + reflexivity.
    + rewrite IHv.
      * f_equal. apply H. now left.
      * intros t Ht sigma'. apply H. now right.
Qed.

Lemma subst_term_map sigma n (t : Vector.t term n) :
  [subst_term' (sigma >> of_term) p | p ∈ to_list (map of_term t)] =
  to_list (map of_term (map (subst_term sigma) t)).
Proof.
  induction t; cbn; trivial.
  now rewrite IHt, subst_term_of_term.
Qed.

Lemma subst_form_of_form sigma phi :
  subst_form' (sigma >> of_term) (of_form phi) = of_form (subst_form sigma phi).
Proof.
  induction phi in sigma |- *; cbn; try congruence.
  - destruct P. cbn. now rewrite subst_term_map.
  - f_equal. rewrite <- IHphi.
    eapply ext_form'. intros []. cbn. reflexivity. cbn.
    now rewrite <- subst_term_of_term.
Qed.

Lemma wf_of_term t :
  { v | wf v (of_term t)}.
Proof.
  induction t using strong_term_ind; cbn.
  - exists isvar. econstructor.
  - destruct F. exists novar. dependent induction v; cbn in *.
    + econstructor.
    + destruct (X h); eauto. apply (wf_app w). eauto.
Qed.

Lemma of_term_wf' v t :
  wf v t -> match v with
           | isvar => exists x, t = var_term' x
           | novar => exists F n (B : Vector.t term n), t = of_term (Func (F, n) B)
	   end.
Proof.
  induction 1; cbn.
  - exists n. reflexivity.
  - exists f, 0, nil. reflexivity.
  - destruct v, IHwf1 as [x Hx], IHwf2 as (f & n & B & Hs); subst.
    + exists f, (S n), (cons (var_term x) B). reflexivity.
    + destruct Hx as (k & C & ->). exists f, (S n), (cons (@Func max (x, k) C) B). reflexivity.
Qed.

Lemma of_term_wf v t :
  wf v t -> exists t', t = of_term t'.
Proof.
  intros H % of_term_wf'. destruct v.
  - destruct H as [x ->]. now exists (var_term x).
  - destruct H as (f & n & B & ->). eauto.
Qed.

Fixpoint wf_form phi :=
  match phi with
  | Fal' => True
  | Pred' P s0 => forall t, t el s0 -> exists v, wf v t
  | Impl' s0 s1 => (wf_form s0) /\ (wf_form s1)
  | All' s0 => wf_form s0
  end.

Lemma wf_of_form phi :
  wf_form (of_form phi).
Proof.
  induction phi; cbn; auto. destruct P. cbn.
  intros s. rewrite <- Vectors.tolist_In.
  intros [s'[<- _]] % Vectors.vect_in_map_iff.
  destruct (wf_of_term s'). now exists x.
Qed.

Lemma of_list_wf A :
  (forall t, t el A -> exists v, wf v t) -> exists n (ts : Vector.t term n), A = to_list (map of_term ts).
Proof.
  induction A; cbn; intros H.
  - exists 0, nil. reflexivity.
  - destruct IHA as (n & ts & ->); eauto.
    destruct (H a) as [v Ha]; auto.
    apply of_term_wf in Ha as [t ->].
    exists (S n), (cons t ts). reflexivity.
Qed.

Lemma of_form_wf phi :
  wf_form phi -> exists phi', phi = of_form phi'.
Proof.
  induction phi; cbn.
  - intros _. exists Fal. reflexivity.
  - intros H. apply of_list_wf in H as (n & ts & ->).
    exists (@Pred max (P, n) ts). reflexivity.
  - intros [H1 H2]. destruct (IHphi1 H1) as [phi1' ->], (IHphi2 H2) as [phi2' ->].
    exists (Impl phi1' phi2'). reflexivity.
  - intros H. destruct (IHphi H) as [phi' ->]. exists (All phi'). reflexivity.
Qed.

Lemma ren_term_to_term xi A t :
  to_term (List.map (subst_term (fun n => var_term (xi n))) A) (subst_term' (fun n => var_term' (xi n)) t)
  = subst_term (fun n => var_term (xi n)) (to_term A t).
Proof.
  induction t in A |- *; cbn; try firstorder congruence.
  - rewrite <- map_rev.
    assert (H : |([subst_term (make_subst xi) p | p ∈ List.rev A])| = |List.rev A|) by now rewrite map_length.
    eapply Func_cast with (H:=H). induction (List.rev A); cbn; trivial. now rewrite IHl.  
  - rewrite (IHt1 List.nil). rewrite <- IHt2. reflexivity.
Qed.

Lemma ren_term_to_term' xi t :
  to_term ([]) (subst_term' (fun n => var_term' (xi n)) t)
  = subst_term (fun n => var_term (xi n)) (to_term ([]) t).
Proof.
  now rewrite <- ren_term_to_term. 
Qed.

Lemma ren_form_to_form xi phi :
  to_form (subst_form' (fun n => var_term' (xi n)) phi) = subst_form (fun n => var_term (xi n)) (to_form phi).
Proof.
  induction phi in xi |- *; cbn; trivial.
  - assert (H : |[to_term ([]) p | p ∈ [subst_term' (fun n => var_term' (xi n)) p | p ∈ args]]|
            = |[to_term ([]) p | p ∈ args]|) by now rewrite !map_length.
    eapply Pred_cast with (H:=H). induction args in H |- *; cbn; trivial.
    rewrite IHargs. now rewrite ren_term_to_term'.
  - now rewrite IHphi1, IHphi2.
  - f_equal. unfold up_term_term'.
    specialize (IHphi (fun n => match n with 0 => 0 | S n => S (xi n) end)).
    erewrite ext_form.
    + rewrite <- IHphi. f_equal. apply ext_form'. now intros [].
    + now intros [].
Qed.

Definition option_pred X (p : X -> Prop) (x : option X) :=
  match x with
  | Some x => p x
  | None => True
  end.

Lemma prvie_prv' A psi phi :
  (forall theta, theta el A -> wf_form theta) -> option_pred wf_form psi -> wf_form phi ->
  sprvie A psi phi -> sprv expl (List.map to_form A) (option_map to_form psi) (to_form phi).
Proof.
  intros H1 H2 H3.
  induction 1; cbn in *; eauto; subst.
  - apply (Contr (phi:=to_form phi)); eauto.
  - destruct H3. apply IR, IHsprvie; trivial.
    intros theta [-> | HT]; auto.
  - eapply AllR. rewrite map_map in *. erewrite map_ext.
    + apply IHsprvie; trivial. intros theta [theta' [<- HT]] % in_map_iff.
      destruct (of_form_wf (H1 theta' HT)) as [psi ->].
      rewrite (ext_form' (tau:= form_shift >> of_term)); try now intros x.
      rewrite subst_form_of_form. apply wf_of_form.
    + intros theta. cbn. now rewrite ren_form_to_form.
  - apply IL; firstorder.
  - apply AllL with (t0:=to_term List.nil t).
    assert (exists t', t = of_term t') as [t' ->] by now eapply of_term_wf.
    assert (exists phi', phi = of_form phi') as [phi' ->] by now apply of_form_wf.
    rewrite to_term_of_term, to_form_of_form.
    erewrite ext_form' in IHsprvie.
    + erewrite subst_form_of_form, to_form_of_form in IHsprvie.
      apply IHsprvie; trivial. apply wf_of_form.
    + intros x. asimpl. now destruct x.
Qed.

Lemma option_map_id A (f : A -> A) o :
  (forall x, f x = x) -> option_map f o = o.
Proof.
  destruct o; cbn.
  - intros. now rewrite H.
  - reflexivity.
Qed.

Lemma option_map_map A B C (f : A -> B) (g : B -> C) o :
  option_map g (option_map f o) = option_map (f >> g) o.
Proof.
  destruct o; cbn.
  - intros. reflexivity.
  - reflexivity.
Qed.

Lemma prvie_prv A psi phi :
  sprvie (List.map of_form A) (option_map of_form psi) (of_form phi) -> sprv expl A psi phi.
Proof.
  intros H % prvie_prv'.
  - rewrite to_form_of_form, map_map in H.
    erewrite map_ext in H. 2: eapply to_form_of_form.
    rewrite map_id, option_map_map, option_map_id in H; trivial.
    eauto using to_form_of_form.
  - intros H [phi'[<- _]] % in_map_iff. apply wf_of_form.
  - destruct psi; cbn; trivial. apply wf_of_form.
  - apply wf_of_form.
Qed.

Lemma prv_prvie A psi phi :
  sprv expl A psi phi -> sprvie (List.map of_form A) (option_map of_form psi) (of_form phi).
Proof.
  induction 1; cbn in *; eauto.
  - eapply ieAllR. rewrite map_map in *.
    erewrite map_ext. eassumption.
    intros; cbn. rewrite <- subst_form_of_form.
    eapply ext_form'. reflexivity.    
  - destruct (wf_of_term t). eapply ieAllL. eassumption. rewrite <- subst_form_of_form in IHsprv.
    erewrite ext_form'. eassumption. intros []; reflexivity. 
Qed.

Import ListNotations.

Instance HdF : eq_dec Funcs.
Proof.
  cbn. exact _.
Qed.

Instance HdP : eq_dec Preds.
Proof.
  cbn. exact _.
Qed.

Instance HeF : enumT Funcs.
Proof.
  cbn. exact _.
Qed.

Instance HeP : enumT Preds.
Proof.
  cbn. exact _.
Qed.

Fixpoint term_eqb (t1 t2 : term') :=
  match t1, t2 with
  | var_term' n, var_term' m => Nat.eqb n m
  | Func' f1, Func' f2 => Nat.eqb f1 f2
  | App' t1 t2, App' t1' t2' => andb (term_eqb t1 t1') (term_eqb t2 t2')
  | _, _ => false
  end.

Lemma term_eqb_spec t1 t2 : reflect (t1 = t2) (term_eqb t1 t2).
Proof.
  induction t1 in t2 |- *; destruct t2; cbn.
  all: try now econstructor; congruence.
  - destruct (Nat.eqb_spec n n0); econstructor; congruence.
  - destruct (Nat.eqb_spec name name0); econstructor; congruence.
  - destruct (IHt1_1 t2_1), (IHt1_2 t2_2).
    all: try now  econstructor; congruence.
Qed.

Instance computable_term_eqb : computable term_eqb.
Proof.
  extract.
Qed.

Definition list_term_eqb := list_eqb term_eqb.

Fixpoint form_eqb (t1 t2 : form') :=
  match t1, t2 with
  | Pred' p1 L1, Pred' p2 L2 => andb (Nat.eqb p1 p2) (list_term_eqb L1 L2)
  | Fal', Fal' => true
  | Impl' t1 t2, Impl' t1' t2' => andb (form_eqb t1 t1') (form_eqb t2 t2')
  | All' phi1, All' phi2 => form_eqb phi1 phi2
  | _, _ => false
  end.

Lemma form_eqb_spec t1 t2 : reflect (t1 = t2) (form_eqb t1 t2).
Proof.
  induction t1 in t2 |- *; destruct t2; cbn.
  all: unfold list_term_eqb in *.
  all: try now econstructor; congruence.
  - destruct (Nat.eqb_spec P P0), (list_eqb_spec term_eqb_spec args args0).
    all: econstructor; congruence.
  - destruct (IHt1_1 t2_1), (IHt1_2 t2_2); econstructor; congruence.
  - destruct (IHt1 t2); econstructor; congruence.
Qed.

Instance computable_list_eqb : computable list_term_eqb.
Proof.
  unfold list_term_eqb.
  extract.
Qed.

Instance computable_form_eqb : computable form_eqb.
Proof.
  extract.
Qed.

Definition list_form_eqb := list_eqb form_eqb.

Definition option_form_eqb := option_eqb form_eqb.

Instance computable_list_form_eqb : computable list_form_eqb.
Proof.
  unfold list_form_eqb.
  extract.
Qed.

Instance computable_option_form_eqb : computable option_form_eqb.
Proof.
  unfold option_form_eqb.
  extract.
Qed.

Definition enum_eqb : (list form' * option form' * form' * (list form' * option form' * form')) -> bool := fun '(A, psi, phi, (A', psi', phi')) => list_form_eqb A A' && option_form_eqb psi psi' && form_eqb phi phi'.

Instance computable_enum_eqb : computable enum_eqb.
Proof.
  extract.
Qed.

(* Instance test : eq_dec form'. *)
(* Proof. *)
(*   intros ? ?. hnf. repeat decide equality. *)
(* Qed. *)

Definition f1 := (fun L_seq : list form' -> option form' -> list form' => fun A => fun phi : form' =>
                                   List.map (Impl' phi) (L_seq (Datatypes.cons phi A) None)).

Instance term_f1 : computable f1.
Proof.
  extract.
Qed.

Definition f2 ( L_seq : option form' -> list form') := (fun psi0 : form' => L_seq (Some psi0) ).

Instance term_f2 : computable f2.
Proof.
  extract.
Qed.

Definition in_eqb a := existsb (form_eqb a).

Instance term_existsb : computable (@existsb form').
Proof.
  extract.
Qed.

Instance computable_ineqb : computable in_eqb.
Proof.
  extract.
Qed.

Lemma in_eqb_spec a L : reflect (List.In a L) (in_eqb a L).
Proof.
  pose proof (existsb_exists (form_eqb a) L).
  unfold in_eqb.
  destruct (existsb (form_eqb a) L).
  - econstructor. destruct H as [? _]. destruct (H eq_refl) as (? & ? & ?).
    eapply (reflect_iff _ _ (form_eqb_spec a x)) in H1. subst. eauto.
  - econstructor. intros ?. destruct H as [_ ?].
    enough (false = true) by congruence.
    eapply H. exists a. split. eauto.
    eapply (reflect_iff _ _ (form_eqb_spec a a)). eauto.
Qed.  

Definition f3 ( L_seq : option form' -> list form') :=
  (fun _ : form' => in_eqb Fal' (L_seq None )).

Instance term_f3 : computable f3.
Proof.
  extract.
Qed.

Definition f4 ( L_seq : option form' -> list form') phi :=
  (fun _ : form' => in_eqb phi (L_seq None )).

Instance term_f4 : computable f4.
Proof.
  extract.
Qed.

Definition f5 ( L_seq : option form' -> list form') psi :=
  (fun t : term' =>
     (L_seq (Some (subst_form' (scons t var_term') psi )) )).

Instance term_scons : computable (@scons term').
Proof.
  extract.
Qed.

Instance term_subst_term' : computable subst_term'.
Proof.
  extract.
Qed.

Definition f6 := (funcomp var_term' shift).

Instance term_f6 : computable f6.
Proof.
  unfold f6, funcomp, shift. extract.
Qed.

Definition f7 (sigma : nat -> term') := sigma >> subst_term' f6.

Instance term_f7 : computable f7.
Proof.
  unfold f7, funcomp, shift. extract.
Qed.

Instance term_up_term_term' : computable up_term_term'.
Proof.
  unfold up_term_term'. unfold var_zero.
  change (computable (fun sigma : fin -> term' => var_term' 0 .: f7 sigma)).
  unfold scons.
  extract.
Qed.
  
Instance term_subst_form' : computable subst_form'.
Proof.
  unfold subst_form'.
  extract. Unshelve. Focus 3.
  split. Lrewrite_generateGoals. 1-5:reflexivity.
    lazymatch goal with
    |- ?s >* ?t =>
    is_ground s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:L.term & computesExp _ _ s v})); solve [shelve]|];
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    lazymatch type of IHInts with
      computes ?ty _ ?v =>
      change v with (@ext _ ty _ (Build_computable IHInts)) in IHR;exact (proj1 IHR)
    end
  end. 
    Unshelve.
    6:  eapply IHP; eauto. 
    Unshelve. 4:{
      eapply extCorrect. }
    Lrewrite. reflexivity. Lproc.
    Intern.cstep.
Qed.

Instance term_f5 : computable f5.
Proof.
  unfold f5. extract.
Qed.

Instance term_form_shift' : computable form_shift'.
Proof.
  extract.
Qed.

Instance term_concat : computable (@concat form').
Proof.
  extract.
Qed.

Fixpoint L_seq n (A : list form') (psi : option form') : list form' :=
  match n with
  | 0 => match psi with Some psi => [psi] | None => A end
  | S n => L_seq n A psi ++
                match psi with
   (* Contr *)  | None => (concat (List.map (f2 (L_seq n A)) A)) ++
   (* IR *)               (concat
                             (List.map
                                (f1 (L_seq n) A)
                                (L_form' n ))) ++
   (* AllR *)             (List.map All'
                                    (L_seq n (List.map (subst_form' form_shift') A) None )) ++
   (* Absurd *)           (filter (f3 (L_seq n A)) (L_form' n )) 
   (* IL *)     | Some (Impl' phi psi) => (filter (f4 (L_seq n A) phi) (L_seq n A (Some psi ) ))
   (* AllL *)   | Some (All' psi) => concat
              (List.map
                 (f5 (L_seq n A) psi) 
                 (L_wf isvar n )) ++ concat
              (List.map
                 (f5 (L_seq n A) psi) 
                 (L_wf novar  n ))
                | _ => []
                end
  end.
Unset Printing Notations.
Print L_seq.
Set Printing Notations.

Instance term_L_seq : computable L_seq.
Proof.
  extract.
Qed.

Opaque in_dec.

Lemma enum_sprv A psi : enum (sprvie A psi) (fun n => L_seq n A psi).
Proof with try (eapply cum_ge' with (L := fun n => L_seq n _ _ ); eauto; omega); try (eapply cum_ge'; eauto; omega).
  repeat split.
  - eauto.
  - rename x into phi. induction 1; try congruence; subst.
    all: unfold f1, f2, f3, f4, f5 in *.
    + destruct IHsprvie as [m]. exists (S m). cbn. in_app 2.
      eapply in_concat_iff. eexists. split. 2: in_collect phi... all: eauto.
    + destruct IHsprvie as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 3.
      eapply in_concat_iff. eexists. split. 2: in_collect phi... in_collect psi...
    + destruct IHsprvie as [m]. exists (S m). cbn. in_app 4. in_collect phi...
    + destruct IHsprvie as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 5.
      match goal with [ |- _ el filter _ _ ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) |  ] | _ => try (rewrite !in_prod_iff; repeat split) end...
      eapply bool_Prop_true.
      rewrite <- reflect_iff. 2:eapply in_eqb_spec. idtac...
    + exists 0. now left.
    + destruct IHsprvie1 as [m1], IHsprvie2 as [m2]. exists (1 + m1 + m2). cbn. in_app 2. match goal with [ |- _ el filter _ _ ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) |  ] | _ => try (rewrite !in_prod_iff; repeat split) end...
      eapply bool_Prop_true.
      rewrite <- reflect_iff. 2:eapply in_eqb_spec. idtac...
    + eapply enum_wf in H. destruct IHsprvie as [m1], H as [m2]. exists (1 + m1 + m2). cbn.
      destruct v.
      * in_app 2. eapply in_concat_iff.
        eexists. split. 2: in_collect t... unfold f5. idtac...
      * in_app 3. eapply in_concat_iff.
        eexists. split. 2: in_collect t... unfold f5. idtac... 
  - intros [m]. induction m in A, psi, x, H |-*; destruct psi; cbn in *.
    + destruct H as [-> | []]. apply ieAx.
    + eauto.
    + unfold f1, f2, f3, f4, f5 in *.
      Ltac inv_collect :=
        repeat
          (match goal with
           | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?)
           | [ H : ?x el List.map _ _ |- _ ] => eapply in_map_iff in H as (? & ? & ?)
           | [ x : ?A * ?B |- _ ] => destruct x; subst
           | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H')
           | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H
           | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as []
           | [H : _ el _ :: _ |- _ ] => destruct H
           end; (try intuition); subst).
      destruct f; inv_collect; eauto.
      * Lemma bool_true_Prop: forall b : bool, b -> b = true.
        Proof.
          destruct b; firstorder.
        Qed.

        eapply bool_true_Prop in H0. rewrite <- reflect_iff in H0. 2: eapply in_eqb_spec.
        eauto.
      * econstructor. 2: eauto. eapply enum_wf. eauto.
      * econstructor. 2: eauto. eapply enum_wf. eauto.
    + unfold f1, f2, f3, f4, f5 in *. destruct b; inv_collect; eauto.
      * eapply bool_true_Prop in H0. rewrite <- reflect_iff in H0. 2: eapply in_eqb_spec.
        eauto.
      * eapply bool_true_Prop in H0. rewrite <- reflect_iff in H0. 2: eapply in_eqb_spec.
        eauto.
Qed.                                                            

Definition T_form_term' := @T_list form' _.
Definition cons''' : form' * list form' -> list form' := fun '(n, L) => n :: L.

Instance term_cons''' : computable cons'''.
Proof.
  extract.
Qed.

Instance term_T_form' : computable T_form_term'.
Proof.
  change (computable
    (fix T_list (n : nat) : list (list form') :=
       match n with
       | 0 => [[]]
       | S n0 => (T_list n0 ++ List.map cons''' (L_form' n0 × T_list n0))%list
       end)).
  extract.
Qed.

Definition f8 (L_seq : list form' -> option form' -> list form') := fun '(A, psi, phi) => in_eqb phi (L_seq A psi).

Instance computable_f8 : computable f8.
Proof.
  extract.
Qed.

Definition f9 (L_seq : list form' -> option form' -> list form') : list form' * option form' * _ -> bool := fun '(A, psi, phi) => in_eqb phi (L_seq A None).

Instance computable_f9 : computable f9.
Proof.
  extract.
Qed.

Fixpoint L_sprvie n :=
  match n with
  | 0  => []
  | S n => L_sprvie n ++
          List.filter (f8 (L_seq n)) (list_prod (list_prod (T_form_term' n) (List.map Some (L_form' n))) (L_form' n)) ++
          List.filter (f9 (L_seq n)) (list_prod (list_prod (T_form_term' n) (List.cons (@None form') List.nil)) (L_form' n)) 
  end.

Instance computable_L_sprvie : computable L_sprvie.
Proof.
  extract.
Qed.

Lemma enum_sprvie : enum (fun '(A, psi, phi) => sprvie A psi phi) L_sprvie.
Proof with try (eapply cum_ge'; eauto; omega).
  repeat split.
  - eauto.
  - destruct x as [[A psi] phi]. intros.
    destruct (el_T A) as [m1].
    destruct (el_T phi) as [m2].
    eapply enum_sprv in H as [m3].
    destruct psi as [psi| ].
    + destruct (el_T psi) as [m4].
      exists (1 + m1 + m2 + m3 + m4).
      cbn. in_app 2.
      eapply in_filter_iff. split.
      rewrite !in_prod_iff. repeat split...
      eapply in_map_iff. repeat esplit; eauto...
      
      unfold f8.
      Set Printing Coercions. eapply bool_Prop_true.
      rewrite <- reflect_iff. 2:eapply in_eqb_spec.
      eapply cum_ge' with (L := (fun n => L_seq n A (Some psi))); eauto; omega.
    + exists (1 + m1 + m2 + m3).
      cbn. in_app 3.
      eapply in_filter_iff. split.
      rewrite !in_prod_iff. repeat split... firstorder.
      unfold f9.
      Set Printing Coercions. eapply bool_Prop_true.
      rewrite <- reflect_iff. 2:eapply in_eqb_spec.
      eapply cum_ge' with (L := (fun n => L_seq n A None)); eauto; omega.
  - intros [m Hm]. destruct x as [[A psi] phi].
    induction m in A, psi, phi, Hm |- *; cbn in *.
    + firstorder.
    + unfold f8, f9 in *. inv_collect.
      * eapply bool_true_Prop in H0. rewrite <- reflect_iff in H0. 2: eapply in_eqb_spec.
        eapply enum_sprv. eauto.
      * eapply bool_true_Prop in H0. rewrite <- reflect_iff in H0. 2: eapply in_eqb_spec.
        eapply enum_sprv. eauto.
Qed.        
