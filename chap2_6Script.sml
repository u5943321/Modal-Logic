open HolKernel Parse boolLib bossLib;

val _ = new_theory "chap2_6";


val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | freevars phi = {x}}`;

val frealizes_def = Define`
  frealizes M c G <=> ?w x. ftype x G /\ w IN M.frame.world /\
                            !σ phi. phi IN G ==> feval M c ((x=+w)σ) phi`;
			    
val isLang_def = Define`
  isLang cset phiset <=> !phi. phi IN phiset ==> fconsts phi ⊆ cset`;



val _ = export_theory();

