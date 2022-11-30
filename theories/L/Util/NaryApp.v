From Undecidability.L Require Import LTactics.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.
Import ListNotations.
Import VectorNotations.
Import L_Notations.

Fixpoint many_lam k s := match k with 0 => s | S k => lam (many_lam k s) end.

Lemma subst_many_lam k n u s :
  subst (many_lam k s) n u = many_lam k (subst s (k + n) u).
Proof.
  induction k in n |- *; cbn.
  - reflexivity.
  - f_equal. rewrite IHk. repeat f_equal. lia.
Qed.

Fixpoint many_app k s (v : Vector.t term k) := 
    match v with
    | Vector.nil => s
    | Vector.cons x _ v => many_app (L.app s x) v
    end.

Lemma subst_many_app k (v : Vector.t term k) n u s :
  subst (many_app s v) n u = many_app (subst s n u) (Vector.map (fun s => subst s n u) v).
Proof.
  induction v in s |- *; cbn.
  - reflexivity.
  - now rewrite IHv.
Qed.

Lemma equiv_many_app_L k (v : Vector.t term k) s t :
  s == t -> many_app s v == many_app t v.
Proof.
  induction v in s, t |- *; intros H; cbn.
  - eassumption.
  - eapply IHv. now rewrite H.
Qed.

Fixpoint tabulate {X : Type} (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n :=
  match n as m return ((Fin.t m -> X) -> t X m) with
  | 0 => fun _ => []
  | S m => fun f => f Fin.F1 :: @tabulate _ m (fun i => f (Fin.FS i))
  end f.

Definition many_vars k := (tabulate (n := k) (fun i => k - S (proj1_sig (Fin.to_nat i)))).

Lemma tabulate_ext {X} k f1 f2 :
  (forall i, f1 i = f2 i :> X) -> tabulate (n := k) f1 = tabulate f2.
Proof.
  intros H. induction k in f1, f2, H |- *; cbn.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma many_vars_S n :
  many_vars (S n) = n :: many_vars n.
Proof.
  cbn. f_equal. unfold many_vars. lia. eapply tabulate_ext. intros i. destruct Fin.to_nat as [i_ Hi].
  reflexivity. 
Qed.

Fixpoint many_subst {k} s n (v : Vector.t term k) := 
  match v with
  | [] => s
  | Vector.cons u k v => many_subst (subst s (n + k) u) n v
  end.
  
Lemma beta_red s t t' : lambda t -> t' == subst s 0 t -> (lam s) t == t'.
Proof.
  intros [u ->] ->. repeat econstructor.
Qed.

Lemma many_beta k (v : Vector.t term k) s : 
  (forall x, Vector.In x v -> proc x) ->
  many_app (many_lam k s) v == many_subst s 0 v.
Proof.
  induction v in s |- *; cbn; intros Hv.
  - reflexivity.
  - rewrite equiv_many_app_L. 2:{ eapply beta_red. eapply Hv. econstructor. reflexivity. }
    rewrite subst_many_lam. replace (n + 0) with n by lia. rewrite IHv. reflexivity.
    intros. eapply Hv. now econstructor.
Qed.

Lemma many_subst_app (s t : term) {k} n (v : Vector.t term k) :
  many_subst (s t) n v = (many_subst s n v) (many_subst t n v).
Proof.
  induction v in n, s, t |- *.
  - reflexivity.
  - cbn. now rewrite IHv.
Qed.

Lemma many_subst_many_app (s : term) {k} n (ts v : Vector.t term k) :
  many_subst (many_app s ts) n v = many_app (many_subst s n v) (Vector.map (fun t => many_subst t n v) ts).
Proof.
  induction v in n, s, ts |- *.
  - cbn. revert ts. apply case0. reflexivity.
  - cbn. apply (caseS' ts). cbn. intros.  
    rewrite subst_many_app, IHv. cbn. rewrite many_subst_app. 
    now rewrite Vector.map_map.
Qed.

Lemma many_subst_closed (s : term) {k} n (v : Vector.t term k) :
  closed s -> many_subst s n v = s.
Proof.
  induction v in n, s |- *.
  - reflexivity.
  - cbn. intros H. rewrite H. now eapply IHv.
Qed.
      