From Undecidability.FOL.Syntax Require Import Core Facts.


From Stdlib Require Import Classes.Init.
From Stdlib Require Import Relation_Definitions.
From Stdlib Require Export Classes.RelationClasses.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Export Setoid.


Section Asimpl.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {ops : operators}.
  Context {ff : falsity_flag}.

  Definition feq {A} {B} (s t : A -> B) := forall x, s x = t x.
  #[local] Notation "a ≡ b" := (feq a b) (at level 51).
  #[local] Notation id := (fun x => x).
  #[global]
  Program Instance feq_reflexive {A} {B}  : Reflexive (@feq A B) | 1.
  Next Obligation. now intros ?. Qed.
  #[global]
  Program Instance feq_symmetrive {A} {B}  : Symmetric (@feq A B) | 1.
  Next Obligation. now intros ?. Qed.
  #[global]
  Program Instance feq_transitive {A} {B}  : Transitive (@feq A B) | 1.
  Next Obligation. intros ?. now rewrite H, H0. Qed.

  #[global]
  Add Parametric Relation A B : (A -> B) (@feq A B)
    reflexivity proved by (feq_reflexive (A:=A))
    symmetry proved by (feq_symmetrive (A:=A))
    transitivity proved by (feq_transitive (A:=A))
    as eq_set_rel.

  #[global]
  Add Parametric Morphism X: (@scons X)
    with signature (@eq X) ==> (@feq nat X) ==> (@feq nat X) as scons_feq.
  Proof.
    intros t x2 y2 H2. intros [|n]; try easy. cbn. now rewrite H2.
  Qed.

  #[global]
  Add Parametric Morphism A B C: (@funcomp A B C)
    with signature (@feq B C) ==> (@feq A B) ==> (@feq A C) as funcomp_feq.
  Proof.
    intros x1 y1 H1 x2 y2 H2. intros k. unfold funcomp. now rewrite H2, H1.
  Qed.

  #[global]
  Add Parametric Morphism : (subst_term)
    with signature (@feq nat term) ==> (@feq term term) as subst_term_feq.
  Proof.
    intros x1 y1 H1. intros x2. apply subst_term_ext, H1.
  Qed.

  #[global]
  Add Parametric Morphism : (subst_term)
    with signature (@feq nat term) ==> (@eq term) ==> (@eq term) as subst_term_feq_eq.
  Proof.
    intros x1 y1 H1. intros x2. apply subst_term_ext, H1.
  Qed.

  #[global]
  Add Parametric Morphism : (subst_form)
    with signature (@feq nat term) ==> (@eq form) ==> (@eq form) as subst_form_feq_eq.
  Proof.
    intros x1 y1 H1. intros x2. apply subst_ext, H1.
  Qed.

  (* Interaction on terms *)
  Lemma asimpl_t_var x s : (var x)`[s] = s x.
  Proof. reflexivity. Qed.
  Lemma asimpl_t_func t v s : (func t v)`[s] = (func t (Vector.map (subst_term s) v)).
  Proof. reflexivity. Qed.
  Lemma asimpl_t_id t : t`[var] = t.
  Proof. now apply subst_term_id. Qed.
  Lemma asimpl_t_comp t s1 s2 : t`[s1]`[s2] = t`[s1 >> subst_term s2].
  Proof. apply subst_term_comp. Qed.
  Lemma asimpl_t_ext t s1 s2 : s1 ≡ s2 -> t`[s1] = t`[s2].
  Proof. apply subst_term_ext. Qed.

  (* Interaction on forms *)
  Lemma asimpl_f_falsity s : falsity[s] = falsity.
  Proof. easy. Qed.
  Lemma asimpl_f_atom P v s : (atom P v)[s] = atom P (Vector.map (subst_term s) v).
  Proof. easy. Qed.
  Lemma asimpl_f_bin b f1 f2 s : (bin b f1 f2)[s] = bin b (f1[s]) (f2[s]).
  Proof. easy. Qed.
  Lemma asimpl_f_quant q f s : (quant q f)[s] = quant q (f[$0 .: (s >> subst_term (S >> var))]).
  Proof. easy. Qed.
  Lemma asimpl_f_id t : t[var] = t.
  Proof. now apply subst_id. Qed.
  Lemma asimpl_f_comp t s1 s2 : t[s1][s2] = t[s1 >> subst_term s2].
  Proof. apply subst_comp. Qed.
  Lemma asimpl_f_ext t s1 s2 : s1 ≡ s2 -> t[s1] = t[s2].
  Proof. apply subst_ext. Qed.

  (* Interaction on forms and terms both uses *)
  Lemma asimpl_vector_nil A B (f:A -> B) : Vector.map f (Vector.nil A) = Vector.nil B.
  Proof. easy. Qed.
  Lemma asimpl_vector_cons A B (f:A -> B) t n v : Vector.map f (@Vector.cons A t n v) = @Vector.cons B (f t) n (Vector.map f v).
  Proof. easy. Qed.

  (* Sigma calculus laws
     Rewritten such that they are always applicable from left to right,
     and so that composition associativity does not affect them ("ca" lemmas)

     Note that they are just given for completeness.
     Since some of them are computational equivalences, we do not actually use them to
     construct the asimpl tactic. *)
  Lemma asimpl_var_id_l s : var >> subst_term s ≡ s.
  Proof. easy. Qed.
  Lemma asimpl_var_id_l_ca X s (t:term -> X) : var >> (subst_term s >> t) ≡ s >> t.
  Proof. easy. Qed.
  Lemma asimpl_subst_merge (t r : nat -> term) : subst_term t >> subst_term r ≡ subst_term (t >> subst_term r).
  Proof. intros n; unfold funcomp. now rewrite subst_term_comp. Qed.
  Lemma asimpl_var_id_r (s : nat->term) : s >> subst_term var ≡ s.
  Proof. intros n. apply asimpl_t_id. Qed.
  Lemma asimpl_id_id_l X Y (f : X -> Y) : id >> f ≡ f.
  Proof. intros x; easy. Qed.
  Lemma asimpl_id_id_r X Y (f : X -> Y) : f >> id ≡ f.
  Proof. intros x; easy. Qed.
  Lemma asimpl_funcomp_assoc X Y Z W (f:X->Y) (g:Y->Z) (h:Z->W) : (f >> g) >> h ≡ f >> (g >> h).
  Proof. intros x; easy. Qed.
  Lemma asimpl_scons_comp Z t s (f : term -> Z) : (t .: s) >> f ≡ ((f t) .: (s >> f)).
  Proof. intros [|n]; easy. Qed.
  Lemma asimpl_up_scons X (t:X) s : S >> (t .: s) ≡ s.
  Proof. now intros [|n]. Qed.
  Lemma asimpl_scons_up : (0 .: S) ≡ id.
  Proof. now intros [|n]. Qed.
  Lemma asimpl_scons_up_f B (f : nat -> B) : (f 0 .: (S >> f)) ≡ f.
  Proof. now intros [|n]. Qed.
End Asimpl.

(* asimpl_pre pushed down substitutions and composes them *)
#[global] Create HintDb asimpl_pre.
#[global] Hint Rewrite -> @asimpl_vector_nil : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_vector_cons : asimpl_pre.

#[global] Hint Rewrite -> @asimpl_t_var : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_t_func : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_t_id : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_t_comp : asimpl_pre.

#[global] Hint Rewrite -> @asimpl_f_falsity : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_f_atom : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_f_bin : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_f_quant : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_f_id : asimpl_pre.
#[global] Hint Rewrite -> @asimpl_f_comp : asimpl_pre.

(* Step 1: Simplify with asimpl_pre *)
#[global] Ltac asimpl_pre := try autorewrite with asimpl_pre.
#[global] Ltac asimpl_pre_in H := try autorewrite with asimpl_pre in H.

#[global] Ltac print_goal := match goal with |- ?g => idtac (* "goal:" g*) end.
#[global] Tactic Notation "debug_idtac" string(x) := idtac (*x*).

(* Step 2: find a place where we use a substitution, and replace it with an evar.
           Bonus asimpl_pre to replace foo[var] with foo (using subst_id) *)
#[global]
Ltac asimpl_match t := (match goal with 
    |- context[?phi[?sigma]] => progress (print_goal; erewrite (@asimpl_f_ext _ _ _ _ phi sigma); [|t]; asimpl_pre)
  | |- context[?tt`[?sigma]] => progress (print_goal; erewrite (@asimpl_t_ext _ tt sigma); [|t]; asimpl_pre) end).


(* Use constr_eq_strict to ensure we are working within the correct goal.
   Otherwise, we modify the goal order, and `progress` thinks we made progress.
   This leads to an endless loop *)
#[global]
Ltac asimpl_match_goal t H := (match goal with 
    H' : context[?phi[?sigma]] |- _ => progress (constr_eq_strict H' H; erewrite (@asimpl_f_ext _ _ _ _ phi sigma) in H; [|t]; try asimpl_pre_in H)
  | H' : context[?tt`[?sigma]] |- _ => progress (constr_eq_strict H' H; erewrite (@asimpl_t_ext _ tt sigma) in H; [|t]; try asimpl_pre_in H) end).

(* Step 3: Simplify the substitution, using the normalizing complete sigma calculus rewrite rules 
           Carefully tune the order such that things are fast. *)
#[global]
Ltac asimpl_on_goal := (cbn; unfold up;
  (match goal with
| |- context[(?a >> ?b) >> ?c] => 
    debug_idtac "asimpl_funcomp_assoc";
    change ((a >> b) >> c) with (a >> (b >> c))
| |- context[var >> subst_term ?s] =>
    debug_idtac "asimpl_var_id_l";
    change (var >> subst_term s) with s 
| |- context[var >> (subst_term ?s >> ?t)] =>
    debug_idtac "asimpl_var_id_l_ca";
    change (var >> (subst_term s >> t)) with (s >> t)
| |- context[id >> ?f] =>
    debug_idtac "asimpl_id_id_l";
    change (id >> f) with f 
| |- context[?f >> id] =>
    debug_idtac "asimpl_id_id_r";
    change (f >> id) with f
| |- context[?s >> subst_term var] =>
    debug_idtac "!asimpl_var_id_r";
    rewrite !(@asimpl_var_id_r _ s)
| |- context[subst_term ?t >> subst_term ?r] =>
    debug_idtac "!asimpl_subst_merge";
    rewrite !(@asimpl_subst_merge _ t r)
| |- context[S >> (?t .: ?s)] =>
    debug_idtac "!asimpl_up_scons";
    rewrite !(@asimpl_up_scons _ t s)
| |- context[(0 .: S)] =>
    debug_idtac "!asimpl_scons_up";
    rewrite ! (@asimpl_scons_up)
| |- context[(?tt .: (S >> ?f))] =>
    debug_idtac "!asimpl_scons_up_f";
    rewrite !(@asimpl_scons_up_f _ f)
| |- context[(?t .: ?s) >> ?f] =>
    debug_idtac "asimpl_scons_comp";
    rewrite (@asimpl_scons_comp _ _ t s f) end)).

(* Do step 3, and resolve the evar with it *)
#[global]
Ltac asimpl_on_goal' := cbn; unfold up; (repeat asimpl_on_goal); reflexivity.

(* General asimpl: Repeat the matching until nothing changes anymore *)
#[global]
Ltac asimpl_base := asimpl_pre; repeat progress asimpl_match (asimpl_on_goal').
#[global]
Ltac asimpl_hyp H := asimpl_pre_in H; repeat progress asimpl_match_goal (asimpl_on_goal') H.

#[global]
Tactic Notation "asimpl" := asimpl_base.
#[global]
Tactic Notation "asimpl" "in" hyp(H) := asimpl_hyp H.

Section Test.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {ff : falsity_flag}.
  Import FragmentSyntax.

  #[local]
  Lemma asimpl_test_1 phi t sigma :
    phi[up sigma][t..] = phi[t.:sigma].
  Proof. 
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_1_ctx phi t sigma :
    phi[up sigma][t..] = phi[t.:sigma] -> (phi[t.:sigma] = phi[t.:sigma]).
  Proof.
    intros H. asimpl in H. apply H.
  Qed.

  #[local]
  Lemma asimpl_test_2 phi :
    phi[up ↑][up (up ↑)][up $0..] = phi[$0 .: S >> ↑].
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_3 phi t sigma :
    phi`[up ↑]`[t.:sigma] = phi`[t.:S>>sigma].
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_4 phi t sigma :
    phi[up ↑][t.:sigma] = phi[t.:S>>sigma].
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_5 phi :
    phi[$0.:↑] = phi.
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_6 phi x :
    phi[up ↑][up $x..] = phi.
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_7 phi :
    phi[up ↑][$0..] = phi.
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_8 phi x :
    phi[up ↑][up $x..][up ↑][up $x..] = phi[up ↑][up $x..][up ↑][up $x..][up ↑][up $x..].
  Proof.
    asimpl. reflexivity.
  Qed.

  #[local]
  Lemma asimpl_test_9 phi :
    phi[up ↑][up (up ↑)][up $0..][up ↑][up (up ↑)][up $0..] = phi[$0 .: S >> S >> ↑].
  Proof.
    asimpl. reflexivity.
  Qed.

End Test.
