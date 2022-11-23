Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.
From Undecidability.HOU Require Import calculus.terms calculus.prelim std.std.

(* * Syntax *)
Definition isVar X (e: exp X) :=
  match e with var _ => True | _ => False end.

Definition isLam X (e: exp X) :=
  match e with lambda _ => True | _ => False end.

Definition isApp X (e: exp X) :=
  match e with app _ _ => True | _ => False end.

Definition isAtom X (e: exp X) :=
  match e with lambda _ => False | app _ _ => False | _ => True end.

Ltac syn :=
  match goal with
  | [H1: isVar ?X, H2: isLam ?X |- _] => solve [destruct X; cbn in *; intuition]
  | [H1: isVar ?X, H2: isApp ?X |- _] => solve [destruct X; cbn in *; intuition]
  | [H1: isApp ?X, H2: isLam ?X |- _] => solve [destruct X; cbn in *; intuition]
  | [H1: isApp ?X, H2: isAtom ?X |- _] => solve [destruct X; cbn in *; intuition]
  | [H1: isLam ?X, H2: isAtom ?X |- _] => solve [destruct X; cbn in *; intuition]
  | [ |- isLam (lambda _)] => constructor
  | [ |- isApp (app _ _)] => constructor
  | [ |- isAtom (var _)] => constructor
  | [ |- isAtom (const _)] => constructor
  | [ |- isVar (var _)] => constructor
  end. 

(* ** Atoms *)
Section Atoms.

  Variable (X: Const).

  Lemma atom_lifting (s: exp X) (sigma: fin -> exp X):
    (forall x, isAtom (sigma x)) -> isAtom s -> isAtom (sigma • s).
  Proof.
    induction s in sigma |-*; cbn; intuition.
  Qed.

  Lemma atom_var (s: exp X):
    isVar s -> isAtom s.
  Proof.
    destruct s; cbn in *; intuition.
  Qed.

End Atoms.


Ltac atom :=
  match goal with
  | [ |- isAtom _] => cbn in *; intuition
  end.    

#[export] Hint Extern 4 => syn : core. 




Section DiscreteTypes.

  Global Instance Const_dis (C: Const) : Dis C.
  Proof.
    eapply const_dis.
  Qed.

  Global Instance exp_dis X: Dis (exp X).
  Proof.
    intros ??; unfold Dec; decide equality. decide equality. eapply const_dis.
  Qed.

  Global Instance type_dis: Dis type.
  Proof.
    intros ??; unfold Dec; decide equality; decide equality.
  Qed. 

End DiscreteTypes.

(* ** Applicative Head *)
Section ApplicativeHead.

  Variable (X: Const).

  Fixpoint head (e: exp X) :=
    match e with
    | const b => const b
    | var x => var x
    | lambda s => lambda s
    | app e1 e2 => head e1
    end.


  Lemma var_head (s: exp X):
    isVar s -> isVar (head s).
  Proof.
    destruct s; cbn; intuition. 
  Qed.

  Lemma atom_head (s: exp X):
    isAtom s -> isAtom (head s).
  Proof.
    destruct s; cbn; intuition. 
  Qed.

  Lemma atom_head_lifting (s: exp X) (sigma: fin -> exp X):
    (forall x, isAtom (head (sigma x))) -> isAtom (head s) -> isAtom (head (sigma • s)).
  Proof.
    induction s; cbn; intuition.
  Qed.

  Lemma head_subst (s: exp X) sigma:
   (forall x, ~ isApp (sigma x))  -> sigma • (head s) = head (sigma • s).
  Proof.
    intros H; induction s.
    - cbn; specialize (H f).
      destruct (sigma f); cbn in *; intuition.
    - reflexivity.
    - reflexivity.
    - cbn; congruence.
  Qed.

End ApplicativeHead.

#[export] Hint Resolve atom_var var_head atom_head : core.


(* ** Type Functions *)
Section TypeFunctions.

  Fixpoint target (A: type) :=
    match A with
    | typevar beta => typevar beta
    | A → B => target B
    end.

  Definition target' (Gamma: list type) :=  map target Gamma.

  Fixpoint arity (A: type) :=
    match A with
    | typevar _ => 0
    | A → B => S (arity B)
    end.

End TypeFunctions.


(* ** Free Variables *)
Section FreeVariables.
  Context {X: Const}.
                             

  Fixpoint vars (s: exp X) :=
    match s with
    | var x => [x]
    | const x => nil
    | lambda s => map pred (remove eq_dec 0 (vars s))
    | app s1 s2 => vars s1 ++ vars s2
    end.

  
  Inductive varof (x: nat) : exp X -> Prop :=
  | varofVar: varof x (var x)
  | varofAppL (s t: exp X): varof x s -> varof x (s t)
  | varofAppR (s t: exp X): varof x t -> varof x (s t)
  | varofLambda s: varof (S x) s -> varof x (lambda s).

  Hint Constructors varof : core.

        
  Lemma varof_vars x s:
    varof x s -> x ∈ vars s.
  Proof.
    induction 1; cbn; eauto.
    1 - 2: eapply in_app_iff; intuition.
    eapply in_map_iff. exists (S x). intuition.
    eapply remove_remain; eauto.
  Qed.

  Lemma vars_varof x s:
    x ∈ vars s -> varof x s.
  Proof.
    induction s in x |-*; cbn; intuition.
    - subst; eauto.
    - econstructor. eapply IHs.
      mapinj. destruct x0.
      + eapply remove_In in H1; intuition.
      + cbn. now eapply remove_prev in H1.
    - simplify in H; intuition. 
  Qed.

  Hint Resolve varof_vars vars_varof : core.

  Global Instance dec_varof: Dec2 (varof). 
  Proof.
    intros x s; eapply iff_dec with (P := x ∈ vars s);
      intuition idtac; auto with typeclass_instances.  
  Qed.

  Lemma subst_extensional sigma tau s:
    (forall x, x ∈ vars s -> sigma x = tau x) -> sigma • s = tau • s.
  Proof.    
    induction s in sigma, tau |-*; eauto.
    - intros H; cbn; f_equal; eapply IHs.
      intros [] ?; cbn; eauto. 
      unfold funcomp; rewrite H; eauto.
    - intros; cbn; erewrite IHs1, IHs2; eauto.
  Qed.


  Lemma varof_ren f x (s: exp X):
    varof x (ren f s) -> exists y, x = f y /\ varof y s.
  Proof.
    induction s in x, f |-*; cbn; intuition.
    - exists f0; intuition. now inv H.
    - inv H.
    - inv H. eapply IHs in H1 as [].
      intuition. destruct x0; try discriminate.
      exists x0. intuition.
    - inv H; [edestruct IHs1 | edestruct IHs2]; eauto; eexists; intuition; eauto.
  Qed.

  Lemma vars_ren f x s:
    x ∈ vars (ren f s) -> exists y, x = f y /\ y ∈ vars s.
  Proof. 
    intros; edestruct varof_ren as [y]; [|exists y]; intuition; eauto.
  Qed.

  Lemma varof_subst x sigma (s: exp X):
    varof x (sigma • s) -> exists y, varof y s /\ varof x (sigma y).
  Proof.
    induction s in sigma, x |-*; cbn.
    - intros; exists f; intuition.
    - inversion 1.
    - intros H; inv H. eapply IHs in H1 as []; intuition.
      destruct x0; cbn in *. inv H1.
      exists (x0); intuition. unfold funcomp in H1.
      now eapply varof_ren in H1 as [y [[= ->] ?]].
    - intros H; inv H; [edestruct IHs1 | edestruct IHs2]; eauto; eexists; intuition; eauto.
  Qed.

    Lemma vars_subst sigma x s:
    x ∈ vars (sigma • s) -> exists y, y ∈ vars s /\ x ∈ vars (sigma y).
  Proof. 
    intros; edestruct varof_subst as [y]; [|exists y]; intuition; eauto.
  Qed.



  Lemma ren_varof x f (s: exp X):
    varof x s -> varof (f x) (ren f s).
  Proof.
    enough (varof x s -> forall y, y = f x -> varof y (ren f s)) by eauto.
    induction 1 in f |-*; cbn; eauto.
    - intros ? ->; eauto.
    - intros ? ->; econstructor; now eapply IHvarof.
  Qed.

  Lemma ren_vars x f (s: exp X):
    x ∈ vars s -> f x ∈ vars (ren f s).
  Proof.
    eauto using ren_varof. 
  Qed.

  Lemma subst_varof x sigma y (s: exp X):
    varof y s -> varof x (sigma y) -> varof x (sigma • s).
  Proof.
    induction 1 in sigma, x |-*; cbn; eauto.
    intros H'; econstructor; eapply IHvarof; cbn; unfold funcomp.
    now eapply ren_varof.
  Qed.

  Lemma subst_vars x sigma y (s: exp X):
    y ∈ vars s -> x ∈ vars (sigma y) -> x ∈ vars (sigma • s).
  Proof.
    eauto using subst_varof. 
  Qed.

  
End FreeVariables.


#[export] Hint Constructors varof : core.
#[export] Hint Resolve varof_vars vars_varof : core.
        

