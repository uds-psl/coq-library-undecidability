(* 
  Problem(s):
    Krivine machine halting (KrivineM_HALT)
    Krivine machine halting for closed terms (KrivineMclosed_HALT)

  Literature:
    [1] Krivine, Jean-Louis.
    "A call-by-name lambda-calculus machine."
    Higher-order and symbolic computation 20.3 (2007): 199-207.

    [2] https://en.wikipedia.org/wiki/Krivine_machine
*)

Require Undecidability.L.L.
Import L (term, var, app, lam).

Require Undecidability.LambdaCalculus.wCBN.
Import wCBN (subst).

(* (closure ctx t) is a lambda-term t in the environment ctx *)
Inductive eterm := closure : list eterm -> term -> eterm.

(* (halt_cbn ts ctx t) is the Krivine machine halting problem
   for the lambda-term t applied to closures ts in the environment ctx;
   this corresponds to weak call-by-name leftmost outermost normalization *)
Inductive halt_cbn : list eterm -> list eterm -> term -> Prop :=
  | halt_var_0 ts ctx t ctx' :
      halt_cbn ts ctx t ->
      halt_cbn ts ((closure ctx t)::ctx') (var 0)
  | halt_var_S ts ctx n t :
      halt_cbn ts ctx (var n) ->
      halt_cbn ts (t::ctx) (var (S n))
  | halt_app ts ctx s t :
      halt_cbn ((closure ctx t)::ts) ctx s ->
      halt_cbn ts ctx (app s t)
  | halt_lam_ts t ts ctx s :
      halt_cbn ts (t::ctx) s ->
      halt_cbn (t::ts) ctx (lam s)
  | halt_lam ctx s :
      halt_cbn nil ctx (lam s).

(* Krivine machine halting *)
Definition KrivineM_HALT : term -> Prop :=
  fun t => halt_cbn nil nil t.

(* Krivine machine halting for closed terms *)
Definition KrivineMclosed_HALT : { t : term | forall sigma, subst sigma t = t } -> Prop :=
  fun '(exist _ t _) => KrivineM_HALT t.
