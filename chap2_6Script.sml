open HolKernel Parse boolLib bossLib;

val _ = new_theory "chap2_6";


val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | freevars phi = {x}}`;

val frealizes_def = Define`
  frealizes M c G <=> ?w x. ftype x G /\ w IN M.frame.world /\
                            !σ phi. phi IN G ==> feval M c ((x=+w)σ) phi`;
			    
val isLang_def = Define`
  isLang cset phiset <=> !phi. phi IN phiset ==> fconsts phi ⊆ cset`;


val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              fnsyms : 'f -> 'a list -> 'a;
		      predsyms : 'p -> 'a list -> bool;
		      |>`;


val mm2folm_def = Define`
  mm2folm M = <| domain := M.frame.world ;
                 fnsyms := \x y. ARB;
		 predsyms := \p. case p of
		             NONE => (\as. case as of [w1;w2] =>
			             M.frame.rel w1 w2 /\
				     w1 IN M.frame.world /\ w2 IN M.frame.world)
			     | SOME pv => \as. case as of [w] =>
			             M.valt p w |>`;




val _ = export_theory();

