open HolKernel Parse boolLib bossLib;

val _ = new_theory "chap2_6";


val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | freevars phi SUBSET {x}}`;

val frealizes_def = Define`
  frealizes M c G <=> ?w x. ftype x G /\ w IN M.domain /\
                            !σ phi. phi IN G ==> feval M c ((x=+w)σ) phi`;
			    
val isLang_def = Define`
  isLang cset phiset <=> !phi. phi IN phiset ==> fconsts phi ⊆ cset`;


























(*

val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              fnsyms : 'f -> 'a list -> 'a;
		      predsyms : 'p -> 'a list -> bool;
		      |>`;

*)

val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              consts : num -> 'a;
	              fnsyms : num -> 'a list -> 'a;
		      predsyms : 'p -> 'a -> bool;
		      relsym : 'a -> 'a -> bool;
		      |>`;


val mm2folm_def = Define`
  mm2folm M = <| domain := M.frame.world ;
                 consts := \n. ARB;
                 fnsyms := \x y. ARB;
		 predsyms := \p w. if p = 0 then (w IN M.frame.world /\ M.valt p w)
		                   else ARB;
		 relsyms := \p w1 w2. if p = 0 then (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) else ARB |>`;

val mm2folm_def = Define`
  mm2folm M = <| domain := M.frame.world ;
                 consts := \n. ARB;
                 fnsyms := \x y. ARB;
		 predsyms := \p w. (w IN M.frame.world /\ M.valt p w);
		 relsym := \w1 w2. (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) |>`;








val expansion_def = Define`
  expansion M A = <| domain := M.domain;
                     consts := \a. 
		     fnsyms := \x y. ARB;
		     pred

val a_saturated_def = Define`
  a_saturated a M = !A. A SUBSET M.domain /\ CARD A < a ==>
                        (!G. ftype x G ==> (!ff. ff IN G ==> ?σ. Models M σ ff)) ==> 
			


(*
val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              fnsyms : 'f -> 'a list -> 'a;
		      predsyms : 'p -> 'a list -> bool;
		      |>`;



                             predsyms := \p. case p of
		             NONE => (\as. case as of [w1;w2] =>
			             M.frame.rel w1 w2 /\
				     w1 IN M.frame.world /\ w2 IN M.frame.world)
			     | SOME pv => \as. case as of [w] =>
			             M.valt p w |>`;
*)




val _ = export_theory();

