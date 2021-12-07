(* * Second-Order Peano Arithmetic *)

Require Import PeanoNat Lia Vector.
From Undecidability.SOL Require Import SOL PA2.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Undecidability.Shared.Libs.PSL Require Import Vectors VectorForall.
From Undecidability.SOL.Util Require Import Syntax Subst Tarski.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Require Import Undecidability.Shared.Dec.

Import VectorNotations SubstNotations SOLNotations PA2Notations.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Derive Signature for Vector.t.
Derive Signature for function.
Derive Signature for predicate.

Unset Implicit Arguments.


(* ** Discreteness and Enumerability *)

#[global]
Instance PA2_funcs_signature_eq_dec :
  eq_dec PA2_funcs_signature.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

#[global]
Instance PA2_preds_signature_eq_dec :
  eq_dec PA2_preds_signature.
Proof.
  intros [] []. now left.
Qed.

Definition L_PA2_funcs (n : nat) := List.cons Zero (List.cons Succ (List.cons Plus (List.cons Mult List.nil))).
Definition L_PA2_preds (n : nat) := List.cons Eq List.nil.

#[global]
Instance PA2_funcs_enum : 
  list_enumerator__T L_PA2_funcs PA2_funcs.
Proof.
  intros []; exists 0; firstorder.
Qed.

#[global]
Instance PA2_preds_enum : 
  list_enumerator__T L_PA2_preds PA2_preds.
Proof.
  intros []; exists 0; firstorder.
Qed.

Lemma PA2_form_enumerable :
  enumerable__T form.
Proof.
  apply form_enumerable.
  - apply list_enumerable__T_enumerable. exists L_PA2_funcs. apply PA2_funcs_enum.
  - apply list_enumerable__T_enumerable. exists L_PA2_preds. apply PA2_preds_enum.
  - apply enumT_binop.
  - apply enumT_quantop.
Qed.

Lemma PA2_enumerable :
  enumerable PA2.
Proof.
  exists (fun n => List.nth n (List.map Some PA2_L) None). intros phi. split.
  - intros H. repeat destruct H as [<-|H]. 
    now exists 0. now exists 1. now exists 2. now exists 3. now exists 4.
    now exists 5. now exists 6. now exists 7. now exists 8. easy.
  - intros [n H]. assert (forall x y : form, Some x = Some y -> x = y) as Some_inj by congruence.
    do 9 try destruct n as [|n]; try apply Some_inj in H as <-. 1-9: firstorder.
    destruct n; cbn in H; congruence.
Qed.

Lemma PA2_closed :
  forall phi, PA2 phi -> closed phi.
Proof.
  intros phi H. repeat destruct H as [<-|H]; cbv; firstorder.
  destruct (Nat.eq_dec ar 1) as [->|]. left; firstorder. right; firstorder.
Qed.

(* Since PA2 is closed, we can characterize validity without requiring to
    satisfy phi in the same environment as PA2 *)
Lemma PA2_valid_alternative phi :
  PA2 ⊨ phi <-> forall M, M ⊨ PA2 -> M ⊨ phi.
Proof.
  split.
  - intros H1 M H2 rho. apply H1. intros psi H3. repeat destruct H3 as [<-|H3]; 
    try apply H2; try easy; clear; firstorder.
  - intros H1 M rho H2. apply H1. intros psi H3. repeat destruct H3 as [<-|H3]; intros rho'. 
    apply (H2 ax_eq_refl). 2: apply (H2 ax_eq_symm). 3: apply (H2 ax_zero_succ). 4: apply (H2 ax_succ_inj). 
    5: apply (H2 ax_add_zero). 6: apply (H2 ax_add_rec). 7: apply (H2 ax_mul_zero). 8: apply (H2 ax_mul_rec). 
    9: apply (H2 ax_ind). 10: easy. all: clear; firstorder. 
Qed.


(* ** Helper Lemmas for working with models of PA2 *)

Section Model.

  Variable M : Model.

  Definition empty_PA2_env M : env (M_domain M) := ⟨ fun n => i_f (M_domain M) Zero ([]) , fun n ar v => i_f (M_domain M) Zero ([]), fun n ar v => True ⟩.

  Hypothesis M_correct : M ⊨ PA2 .

  Notation "'izero'" := (@i_f _ _ (M_domain M) (M_interp M) Zero ([])).
  Notation "'iσ' x" := (@i_f _ _ (M_domain M) (M_interp M) Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_f _ _ (M_domain M) (M_interp M) Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_f _ _ (M_domain M) (M_interp M) Mult ([x ; y])) (at level 38).
  Notation "x 'i==' y" := (@i_P _ _ (M_domain M)  (M_interp M) Eq ([x ; y])) (at level 40).

  Lemma eq_reflexive x :
    x i== x.
  Proof. revert x. apply (M_correct ax_eq_refl ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma eq_symm x y :
    x i== y -> y i== x.
  Proof. apply (M_correct ax_eq_symm ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma zero_succ' x :
    izero i== iσ x -> False.
  Proof. apply (M_correct ax_zero_succ ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma succ_inj' x y :
    iσ x i== iσ y -> x i== y.
  Proof. apply (M_correct ax_succ_inj ltac:(firstorder) (empty_PA2_env _)). Qed.

  (* Simplify induction axiom by removing the vector *)
  Lemma induction (P : M_domain M -> Prop) :
    P izero -> (forall x, P x -> P (iσ x)) -> forall x, P x.
  Proof.
    pose (P' := fun v : vec _ 1 => P (Vector.hd v)).
    change (P' ([izero]) -> (forall x, P' ([x]) -> P' ([iσ x])) -> forall x, P' ([x])).
    apply (M_correct ax_ind ltac:(firstorder) (empty_PA2_env _)).
  Qed.

  Lemma case_analysis x :
    x = izero \/ exists x', x = iσ x'.
  Proof.
    revert x. apply induction.
    - now left.
    - intros x _. right. now exists x.
  Qed.

  Lemma eq_sem x y :
    x i== y <-> x = y.
  Proof.
    split.
    - revert x y. apply (induction (fun x => forall y, x i== y -> x = y)).
      + intros y H. destruct (case_analysis y) as [->|[y' ->]].
        * reflexivity. 
        * now apply zero_succ' in H.
      + intros x IH y H. destruct (case_analysis y) as [->|[y' ->]].
        * now apply eq_symm, zero_succ' in H.
        * rewrite (IH y'). reflexivity. now apply succ_inj'.
    - intros ->. apply eq_reflexive.
  Qed.

  Lemma zero_succ x :
    izero = iσ x -> False.
  Proof. intros H%eq_sem. now apply (zero_succ' x). Qed.

  Lemma succ_inj x y :
    iσ x = iσ y -> x = y.
  Proof. intros H%eq_sem. now apply eq_sem, (succ_inj' x y). Qed.

  Lemma add_zero x :
    izero i⊕ x = x.
  Proof. apply eq_sem, (M_correct ax_add_zero ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma add_rec x y :
    iσ x i⊕ y = iσ (x i⊕ y).
  Proof. apply eq_sem, (M_correct ax_add_rec ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma mul_zero x :
    izero i⊗ x = izero.
  Proof. apply eq_sem, (M_correct ax_mul_zero ltac:(firstorder) (empty_PA2_env _)). Qed.

  Lemma mul_rec x y :
    iσ x i⊗ y = y i⊕ (x i⊗ y).
  Proof. apply eq_sem, (M_correct ax_mul_rec ltac:(firstorder) (empty_PA2_env _)). Qed.


  (* Convert from nat to this model *)

  Fixpoint to_domain n : M_domain M := match n with
    | 0 => izero
    | S n => iσ (to_domain n)
  end.

  Lemma to_domain_add x y :
    to_domain (x + y) = to_domain x i⊕ to_domain y.
  Proof.
    revert y. induction x; intros; cbn.
    - symmetry. apply add_zero.
    - rewrite add_rec. now repeat f_equal.
  Qed.

  Lemma to_domain_mul x y :
    to_domain (x * y) = to_domain x i⊗ to_domain y.
  Proof.
    revert y. induction x; intros; cbn.
    - symmetry. apply mul_zero.
    - rewrite mul_rec. rewrite to_domain_add. now repeat f_equal.
  Qed.

  Lemma to_domain_injective x x' :
    to_domain x = to_domain x' -> x = x'.
  Proof.
    revert x'. induction x; destruct x'.
    - reflexivity.
    - now intros H%zero_succ.
    - intros H. symmetry in H. now apply zero_succ in H.
    - intros H%succ_inj. now rewrite (IHx x').
  Qed.

End Model.



(* ** Standard Model *)

Section StandardModel.

  Definition std_interp_f (f : syms) : vec nat (ar_syms f) -> nat :=
    match f with
      | Zero => fun _ => 0
      | Succ => fun v => S (Vector.hd v)
      | Plus => fun v => Vector.hd v + Vector.hd (Vector.tl v)
      | Mult => fun v => Vector.hd v * Vector.hd (Vector.tl v)
    end.

  Definition std_interp_P (P : preds) : vec nat (ar_preds P) -> Prop :=
    match P with
      | Eq => fun v => Vector.hd v = Vector.hd (Vector.tl v)
    end.

  Instance I_nat : interp nat := {| i_f := std_interp_f ; i_P := std_interp_P |}.

  Definition Standard_Model : Model := {|
    M_domain := nat ;
    M_interp := I_nat
  |}.

  Lemma std_model_correct : 
    Standard_Model ⊨ PA2.
  Proof.
    intros phi H. repeat try destruct H as [<-|H]; hnf; cbn; try congruence.
    intros rho P H IH n. induction n; auto. easy.
  Qed.

End StandardModel.



(* ** Signature Embedding *)

(* We can embed the PA2 signature into the formula and translate to
    an arbitrary signature. *)

Section EmbedSignature.

  Definition Σf := PA2_funcs_signature.
  Definition Σp := PA2_preds_signature.
  Context {Σf' : funcs_signature}.
  Context {Σp' : preds_signature}.
  Context {D : Type}.
  Context {I : @interp Σf Σp D}.
  Context {I' : @interp Σf' Σp' D}.

  (* We assume that the PA2 functions and predicates are inside the
     environment at

        xO = Position of zero
        xS = Position of succ
        xA = Position of add
        xA + 1 = Position of mul

     Replace function and predicate symbols with the corresponding
     variable and shift the existing variables. 
  *)

  Fixpoint embed_term xO xS xA (t : @term Σf) : @term Σf' := match t with
    | var_indi x => var_indi x
    | func (sym Zero) v => func (@var_func _ xO 0) (Vector.map (embed_term xO xS xA) v)
    | func (sym Succ) v => func (@var_func _ xS 1) (Vector.map (embed_term xO xS xA) v)
    | func (sym Plus) v => func (@var_func _ xA 2) (Vector.map (embed_term xO xS xA) v)
    | func (sym Mult) v => func (@var_func _ (S xA) 2) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 0) v => if Compare_dec.le_lt_dec xO x then func (@var_func _ (S x) 0) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 0) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 1) v => if Compare_dec.le_lt_dec xS x then func (@var_func _ (S x) 1) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 1) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 2) v => if Compare_dec.le_lt_dec xA x then func (@var_func _ (S (S x)) 2) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 2) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x ar) v => func (@var_func _ x ar) (Vector.map (embed_term xO xS xA) v)
  end.

  Fixpoint embed_form xO xS xA xEq (phi : @form Σf Σp _) : @form Σf' Σp' _ := match phi with
    | fal => fal
    | atom (pred Eq) v => atom (@var_pred _ xEq 2) (Vector.map (embed_term xO xS xA) v)
    | atom (@var_pred _ x 2) v => if Compare_dec.le_lt_dec xEq x then atom (@var_pred _ (S x) 2) (Vector.map (embed_term xO xS xA) v) else atom (@var_pred _ x 2) (Vector.map (embed_term xO xS xA) v)
    | atom (@var_pred _ x ar) v => atom (@var_pred _ x ar) (Vector.map (embed_term xO xS xA) v)
    | bin op phi psi => bin op (embed_form xO xS xA xEq phi) (embed_form xO xS xA xEq psi)
    | quant_indi op phi => quant_indi op (embed_form xO xS xA xEq phi)
    | quant_func op 0 phi => quant_func op 0 (embed_form (S xO) xS xA xEq phi)
    | quant_func op 1 phi => quant_func op 1 (embed_form xO (S xS) xA xEq phi)
    | quant_func op 2 phi => quant_func op 2 (embed_form xO xS (S xA) xEq phi)
    | quant_func op ar phi => quant_func op ar (embed_form xO xS xA xEq phi)
    | quant_pred op 2 phi => quant_pred op 2 (embed_form xO xS xA (S xEq) phi)
    | quant_pred op ar phi => quant_pred op ar (embed_form xO xS xA xEq phi)
  end.

  Definition pred n := match n with 0 => 0 | S n => n end.

  (* Predicate that states that rho' contains the PA2 signature inserted at
      positions xO, xS, xA and xEq, and matches up with rho. *)
  Definition env_contains_PA2 (rho rho' : env D) xO xS xA xEq :=
    (forall n, get_indi rho n = get_indi rho' n) /\
    (forall n ar, get_func rho' n ar = match ar with 
        | 0 => match Compare_dec.lt_eq_lt_dec n xO with inleft (left _) => get_func rho n 0 | inleft (right _) => @i_f _ _ D I Zero | inright _ => get_func rho (pred n) 0 end
        | 1 => match Compare_dec.lt_eq_lt_dec n xS with inleft (left _) => get_func rho n 1 | inleft (right _) => @i_f _ _ D I Succ | inright _ => get_func rho (pred n) 1 end
        | 2 => if Nat.eq_dec n xA then @i_f _ _ D I Plus else match Compare_dec.lt_eq_lt_dec n (S xA) with inleft (left _) => get_func rho n 2 | inleft (right _) => @i_f _ _ D I Mult | inright _ => get_func rho (pred (pred n)) 2 end
        | ar => get_func rho n ar
      end) /\
    (forall n ar, get_pred rho' n ar = match ar with
        | 2 => match Compare_dec.lt_eq_lt_dec n xEq with inleft (left _) => get_pred rho n 2 | inleft (right _) => @i_P _ _ D I Eq | inright _ => get_pred rho (pred n) 2 end
        | ar => get_pred rho n ar
      end).

  Local Arguments Nat.eq_dec : simpl never.
  Local Arguments Compare_dec.lt_eq_lt_dec : simpl never.

  Ltac solve_env E :=
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia; cbn; try rewrite E;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia; cbn; try rewrite E;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia.

  Lemma env_contains_PA2_scons_i rho rho' xO xS xA xEq d :
    env_contains_PA2 rho rho' xO xS xA xEq -> env_contains_PA2 ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ ⟨d .: get_indi rho', get_func rho', get_pred rho'⟩ xO xS xA xEq.
  Proof.
    intros E. split. 2: apply E. intros []. reflexivity. apply E.
  Qed.

  Lemma env_contains_PA2_scons_f {rho rho' xO xS xA xEq ar} (f : vec D ar -> D) :
    env_contains_PA2 rho rho' xO xS xA xEq ->
    match ar with
      | 0 => env_contains_PA2 ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ (S xO) xS xA xEq
      | 1 => env_contains_PA2 ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO (S xS) xA xEq
      | 2 => env_contains_PA2 ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO xS (S xA) xEq
      | ar => env_contains_PA2 ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO xS xA xEq
    end.
  Proof.
    intros E. unfold econs, econs_func, econs_ar. destruct ar as [|[|[]]];
    split; try apply E; split; try apply E; destruct E as [_ [E2 _]];
    intros [|[|[]]] [|[|[]]]; solve_env E2; reflexivity.
  Qed.

  Lemma env_contains_PA2_scons_p {rho rho' xO xS xA xEq ar} (P : vec D ar -> Prop) :
    env_contains_PA2 rho rho' xO xS xA xEq ->
    match ar with
      | 2 => env_contains_PA2 ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ ⟨get_indi rho', get_func rho', P .: get_pred rho'⟩ xO xS xA (S xEq)
      | _ => env_contains_PA2 ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ ⟨get_indi rho', get_func rho', P .: get_pred rho'⟩ xO xS xA xEq
    end.
  Proof.
    intros E. unfold econs, econs_func, econs_ar. destruct ar as [|[|[]]];
    split; try apply E; split; try apply E; destruct E as [_ [_ E3]];
    intros [|[|[]]] [|[|[]]]; solve_env E3; reflexivity.
  Qed.

  Lemma embed_term_correct rho rho' xO xS xA xEq t :
    env_contains_PA2 rho rho' xO xS xA xEq -> @eval Σf Σp D I rho t = @eval Σf' Σp' D I' rho' (embed_term xO xS xA t).
  Proof.
    intros E. induction t; cbn.
    - apply E.
    - destruct E as [_ [E2 _]]. apply map_ext_forall in IH. destruct ar as [|[|[]]];
      try destruct Compare_dec.le_lt_dec; cbn; rewrite E2;
      try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
      try destruct Nat.eq_dec; try lia; now rewrite map_map, IH.
    - destruct E as [_ [E2 _]]. apply map_ext_forall in IH. destruct f; cbn in *; 
      rewrite E2; destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
      try destruct Nat.eq_dec; try lia; now rewrite map_map, IH.
  Qed.

  Lemma embed_form_correct rho rho' xO xS xA xEq phi :
    env_contains_PA2 rho rho' xO xS xA xEq -> @sat Σf Σp D I rho phi <-> @sat Σf' Σp' D I' rho' (embed_form xO xS xA xEq phi).
  Proof.
    revert rho rho' xO xS xA xEq. induction phi; intros rho rho' xO xS xA xEq E; cbn.
    - reflexivity.
    - assert (map (@eval Σf Σp D I rho) v = map (fun t => @eval Σf' Σp' D I' rho' (embed_term xO xS xA t)) v) as Hv'.
      { clear p. induction v. reflexivity. cbn; f_equal. 
        apply (embed_term_correct _ _ _ _ _ _ _ E). apply IHv. }
      destruct E as [_ [_ E3]]. destruct p; cbn.
      + destruct ar as [|[|[]]];
        try destruct Compare_dec.le_lt_dec; cbn; rewrite E3;
        try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
        now rewrite map_map, Hv'.
      + destruct P; cbn in *. rewrite E3.
        destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia.
        now rewrite map_map, Hv'.
    - specialize (IHphi1 rho rho' xO xS xA xEq E);
      specialize (IHphi2 rho rho' xO xS xA xEq E).
      destruct b; tauto.
    - destruct q.
      + split; intros H d; eapply IHphi. 2,4: apply (H d). all: now apply env_contains_PA2_scons_i.
      + split; intros [d H]; exists d; eapply IHphi. 2,4: apply H. all: now apply env_contains_PA2_scons_i.
    - destruct q; destruct n as [|[|[]]]; split.
      1-8: intros H f; eapply IHphi; try apply (H f); try apply H; now apply (env_contains_PA2_scons_f f).
      all: intros [f H]; exists f; eapply IHphi; try apply (H f); try apply H; now apply (env_contains_PA2_scons_f f).
    - destruct q; destruct n as [|[|[]]]; split.
      1-8: intros H P; eapply IHphi; try apply (H P); try apply H; now apply (env_contains_PA2_scons_p P).
      all: intros [P H]; exists P; eapply IHphi; try apply (H P); try apply H; now apply (env_contains_PA2_scons_p P).
  Qed.

End EmbedSignature.



(* Now we can translate satisfiability and validity for arbitrary models
    over arbitrary signatures to PA2 models. *)

Section PA2ValidSatTranslation.

  Context `{Σf' : funcs_signature}.
  Context `{Σp' : preds_signature}.

  (* Encode axioms into formula *)
  Definition PA2_form :=
    ax_eq_refl ∧ ax_eq_symm ∧ ax_zero_succ ∧ ax_succ_inj ∧ ax_add_zero ∧ ax_add_rec ∧ ax_mul_zero ∧ ax_mul_rec ∧ ax_ind.

  Lemma PA2_Model_sat_PA2_form M :
    forall rho, (M, rho) ⊨ PA2 <-> (M, rho) ⊨ PA2_form.
  Proof.
    intros rho. split.
    - intros M_correct. repeat split; apply M_correct; repeat (try (left; reflexivity); try right).
    - intros H. intros phi H1. repeat destruct H1 as [<-|H1]; try apply H; try easy.
  Qed.

  Lemma PA2_model_valid_iff_model_valid (phi : @form PA2_funcs_signature PA2_preds_signature _) :
    (forall M rho, (M, rho) ⊨ PA2 -> (M, rho) ⊨ phi) <-> (forall M' rho, (M', rho) ⊨ (∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (embed_form 0 0 0 0 (PA2_form ~> phi)))).
  Proof.
    split.
    - intros H M' rho fO fS fM fA pE.
      pose (I := @B_I PA2_funcs_signature PA2_preds_signature _ 
                    (fun f => match f with Zero => fO | Succ => fS | Plus => fA | Mult => fM end)
                    (fun P => match P with Eq => pE end )).
      pose (M := {| M_domain := M_domain M' ; M_interp := I |}).
      eapply (embed_form_correct rho).
      + cbn. split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
      + intros H_PA2. apply (H M), PA2_Model_sat_PA2_form, H_PA2.
    - intros H M rho M_correct. 
      pose (I' := {| i_f _ _ := @i_f _ _ _ (M_interp M) Zero ([]) ; i_P _ _ := True |} ).
      pose (M' := {| M_domain := M_domain M ; M_interp := I' |}).
      pose (zero' := @i_f _ _ _ (M_interp M) Zero);  pose (succ := @i_f _ _ _ (M_interp M) Succ); pose (plus := @i_f _ _ _ (M_interp M) Plus);  pose (mult := @i_f _ _ _ (M_interp M) Mult); pose (equal := @i_P _ _ _ (M_interp M) Eq).
      specialize (H M' rho zero' succ mult plus equal).
      eapply embed_form_correct in H.
      + apply H. apply -> PA2_Model_sat_PA2_form. apply M_correct.
      + split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
  Qed.

  Lemma PA2_model_sat_iff_model_sat (phi : @form PA2_funcs_signature PA2_preds_signature _) :
    (exists M rho, (M, rho) ⊨ PA2 /\ (M, rho) ⊨ phi) <-> (exists M' rho, (M', rho) ⊨ (∃f(0) ∃f(1) ∃f(2) ∃f(2) ∃p(2) (embed_form 0 0 0 0 (PA2_form ∧ phi)))).
  Proof.
    split.
    - intros [M [rho H]].
      pose (I' := @B_I Σf' Σp' _ (fun f _ => @i_f _ _ _ (M_interp M) Zero ([])) (fun P _ => True )).
      pose (M' := {| M_domain := M_domain M ; M_interp := I' |}).
      exists M', rho.
      exists (@i_f _ _ _ (M_interp M) Zero), (@i_f _ _ _ (M_interp M) Succ), (@i_f _ _ _ (M_interp M) Mult), (@i_f _ _ _ (M_interp M) Plus), (@i_P _ _ _ (M_interp M) Eq).
      eapply (embed_form_correct rho).
      + cbn. split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
      + split. now apply -> PA2_Model_sat_PA2_form. apply H.
    - intros [M' [rho [fO [fS [fM [fA [pE H]]]]]]]; cbn -[embed_form] in H.
      pose (I := @B_I PA2_funcs_signature PA2_preds_signature _ 
                    (fun f => match f with Zero => fO | Succ => fS | Plus => fA | Mult => fM end)
                    (fun P => match P with Eq => pE end )).
      pose (M := {| M_domain := M_domain M' ; M_interp := I |}).
      exists M, rho. eapply (embed_form_correct rho) in H.
      + split. apply PA2_Model_sat_PA2_form, H. apply H.
      + split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
  Qed.

  Definition embed_PA2 phi := ∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (@embed_form Σf' Σp' 0 0 0 0 (PA2_form ~> phi)).

  Lemma PA2_sat_iff_empty_theory_sat (phi : @form PA2_funcs_signature PA2_preds_signature _) :
    PA2 ⊨ phi <-> (fun _ => False) ⊨ embed_PA2 phi.
  Proof.
    split.
    - intros H M rho HM. now apply PA2_model_valid_iff_model_valid.
    - intros H M. apply PA2_model_valid_iff_model_valid. intros M' rho. now apply (H M').
  Qed.

End PA2ValidSatTranslation.
