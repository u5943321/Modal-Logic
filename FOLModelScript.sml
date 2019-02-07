open HolKernel Parse boolLib bossLib;
open FOLSyntaxTheory;


val _ = new_theory "FOLModel";

(*

val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              consts : num -> 'a;
	              fnsyms : num -> 'a list -> 'a;
		      predsyms : 'p -> 'a -> bool;
		      relsyms : 'p -> 'a -> 'a -> bool;
		      |>`;

val interpret_def = Define`
  interpret M σ (fVar n) = σ n /\
  interpret M σ (fConst n) = M.consts n`;


val Models_def = Define`
  Models M σ (fPrel a t) = M.predsyms a (interpret M σ t) /\
  Models M σ (fRrel a t1 t2) = M.relsyms a (interpret M σ t1) (interpret M σ t2) /\
  Models M σ (fDISJ f1 f2) = (Models M σ f1 \/  Models M σ f2) /\
  Models M σ (fNOT f) = ¬(Models M σ f) /\
  Models M σ (fEXISTS n f) = (?x. x IN M.domain /\ Models M ((n=+x)σ) f) /\
  Models M σ (fEQ t1 t2) = (interpret M σ t1 = interpret M σ t2)`;


*)

val _ = export_theory();

