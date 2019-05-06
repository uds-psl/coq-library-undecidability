From Undecidability.L Require Import L.

(* Problems concerning the call-by-value lambda-calculus *)

(* Call-by-Value Lambda Calculus as a Model of Computation in Coq. Yannick Forster and Gert Smolka. Journal of Automated Reasoning (2018). https://www.ps.uni-saarland.de/extras/L-computability/ *)

Definition HaltL s := exists t, eval s t. (* Halting problem for call-by-value lambda-calculus *)

Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t. (* Halting problem for call-by-value lambda-calculus *)
