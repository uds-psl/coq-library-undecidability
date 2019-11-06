(** ** Signature Compression *)

Require Import Equations.Equations Fin.
From Undecidability.FOLP Require Export FullTarski.

Section Compression.

  Context { Sigma : Signature }.

  Notation fin := Fin.t.

  Variables (pred_count : nat) (pred : fin pred_count -> Preds) (index : Preds -> fin pred_count).
  Hypothesis pred_index : forall P, pred (index P) = P.

  Definition fin_max n (f : fin n -> nat) :
    { k | forall i : fin n, f i <= k }.
  Proof.
    induction n.
    - exists 0. intros i. inversion i.
    - destruct (IHn (fun i => f (FS i))) as [k Hk].
      destruct (le_ge_dec (f F1) k) as [H|H].
      + exists k. intros i. depelim i; trivial.
      + exists (f F1). intros i. depelim i; trivial.
        specialize (Hk i). rewrite Hk. apply H.
  Defined.

  Definition pred_max :=
    proj1_sig (fin_max (fun i => pred_ar (pred i))).

  Lemma pred_max_spec :
    forall P, pred_ar P <= pred_max.
  Proof.
    intros P.
    unfold pred_max. rewrite <- pred_index at 1. generalize (index P). apply proj2_sig.
  Qed.

  Definition compress_sig :=
    {| Funcs := Funcs; fun_ar := fun_ar; Preds := unit; pred_ar := fun _ => S pred_max |}.

  Fixpoint convert_t (t : @term Sigma) : @term compress_sig :=
    match t with
    | var_term s => var_term s
    | Func f v => @Func compress_sig f (Vector.map convert_t v)
    end.

  Definition convert_v n (v : vector term n) :=
    Vector.map convert_t v.

  Fixpoint vec_tab n X (x0 : X) : vector X n :=
    match n with 
    | 0 => Vector.nil
    | S n => Vector.cons x0 (vec_tab n x0)
    end.

  Definition fill n k X (v : vector X n) (x0 : X) :
    n <= k -> vector X k.
  Proof.
    intros H.
    refine (cast (Vector.append v (vec_tab (k-n) x0)) _). abstract lia.
  Defined.

  Definition index_nat P :=
    proj1_sig (to_nat (index P)).
  
  Definition encode_v P (v : vector term (pred_ar P)) :=
    Vector.cons (var_term (index_nat P)) (fill (convert_v v) (var_term 0) (pred_max_spec P)).

  Fixpoint encode' (n : nat) (phi : @form Sigma) : @form compress_sig :=
    match phi with
    | Pred P v => @Pred compress_sig tt (encode_v v)
    | Fal => Fal
    | Impl phi psi => Impl (encode' n phi) (encode' n psi)
    | Conj phi psi => Conj (encode' n phi) (encode' n psi)
    | Disj phi psi => Disj (encode' n phi) (encode' n psi)
    | Ex phi => Ex (encode' (S n) phi)
    | All phi => All (encode' (S n) phi)
    end.


End Compression.
