Require Import NAxioms NSub NZDiv.
Module Type NDivProp (Import N : NAxiomsSig')(Import NP : NSubProp N).
Module Import Private_NZDiv := Nop <+ NZDivProp N N NP.


Compute (2/2).

(* Theorem a_div_five_imp_a_div_twofive :
  forall a, 5 / a -> 5 / 2a. *)
