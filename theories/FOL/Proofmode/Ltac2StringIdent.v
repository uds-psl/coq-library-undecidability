(* Originally developed by Tej Chajed for the Iris proof mode.
 * See: https://gitlab.mpi-sws.org/iris/string-ident/-/tree/master
 *
 * Adapted to use MetaCoq instead of Ltac2 by Johannes Hostert.
 * 
 * Also see https://github.com/coq/coq/issues/7922 *)

(*
License:

All files in this development are distributed under the terms of the BSD
license, included below.

Copyright: Iris developers and contributors

------------------------------------------------------------------------------

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)


From MetaCoq.Template Require Import All.
MetaCoq Quote Definition qUnit := unit.
Definition unitFunc k := tLambda {| binder_name := nNamed k; binder_relevance := Relevant |} qUnit (tRel 0).
Ltac coq_string_to_ident_lambda' s :=
  let k v := exact v in
  run_template_program (tmUnquoteTyped (unit->unit) (unitFunc s)) k. 
Ltac string_to_ident s :=
  let x := constr:(ltac:(coq_string_to_ident_lambda' s) : unit -> unit) in
  match x with
  | (fun (name:_) => _) => name
  end.
