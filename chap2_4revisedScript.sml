open HolKernel Parse boolLib bossLib;
open combinTheory;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open finite_mapTheory;
open chap1Theory;
open chap2_5Theory;

val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_4";

val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              consts : num |-> 'a;
	              fnsyms : num -> 'a list -> 'a;
		      predsyms : 'p -> 'a -> bool;
		      relsyms : 'r -> 'a -> 'a -> bool;
		      |>`;

val mm2folm_def = Define`
  mm2folm M = <| domain := M.frame.world ;
                 consts := FEMPTY;
                 fnsyms := \x y. ARB;
		 predsyms := \p w. (w IN M.frame.world /\ M.valt p w);
		 relsyms := \ (u:unit) w1 w2. (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) |>`;

val expansion_def = Define`
  expansion M0 A M <=> A SUBSET M0.domain /\
                       ?ns f. ns INTER (FDOM M0.consts) = {} /\
		       BIJ f ns A /\
		       FINITE A /\
		       M = M0 with consts := FUNION M0.consts (FUN_FMAP f ns)`;
                       

val _ = Datatype`
        fterm = fVar num
	       | fConst num ;
	fform = fRrel 'r fterm fterm
	       | fPrel 'p fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`; 

val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;


val ST_def = Define`
  (ST x (u:unit) (VAR p) <=> fPrel p (fVar x)) /\
  (ST x u (FALSE) <=> fNOT (fEQ (fVar x) (fVar x))) /\
  (ST x u (NOT phi) <=> fNOT (ST x u phi)) /\
  (ST x u (DISJ phi psi) <=> fDISJ (ST x u phi) (ST x u psi)) /\
  (ST x u (DIAM phi) <=> fEXISTS (x + 1) (fAND (fRrel u (fVar x) (fVar (x + 1))) (ST (x + 1) u phi)))`;


val interpret_def = Define`
  interpret M σ (fVar n) = σ n /\
  interpret M σ (fConst n) = M.consts ' n`;


val feval_def = Define`
  feval M σ (fPrel p t) = M.predsyms p (interpret M σ t) /\
  feval M σ (fRrel (u:unit) t1 t2) = M.relsyms u (interpret M σ t1) (interpret M σ t2) /\
  feval M σ (fDISJ f1 f2) = (feval M σ f1 \/ feval M σ f2) /\
  feval M σ (fNOT f) = ¬(feval M σ f) /\
  feval M σ (fEXISTS n f) = (?x. x IN M.domain /\ feval M ((n=+x)σ) f) /\
  feval M σ (fEQ t1 t2) = (interpret M σ t1 = interpret M σ t2)`;



val fsatis_def = Define`
  fsatis M σ fform <=> (IMAGE σ univ(:num)) SUBSET M.domain /\
                       feval M σ fform`;


val prop_2_47_i = store_thm(
  "prop_2_47_i",
  ``!M w:'b phi σ x. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ x) phi <=> fsatis (mm2folm M) σ (ST x (u:unit) phi))``,
  Induct_on `phi` >> rw[] (* 5 *)
  >- (rw[feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- fs[mm2folm_def]
     >- (fs[satis_def] >> rw[interpret_def] >> fs[mm2folm_def,IN_DEF])
     >- (rw[satis_def] >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
                      >- (fs[interpret_def] >> fs[mm2folm_def,IN_DEF])))
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 5 *)
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- rw[]
     >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- fs[mm2folm_def]
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- fs[mm2folm_def]
	>- (fs[interpret_def,APPLY_UPDATE_THM] >> rw[mm2folm_def])
	>- (`((x + 1 =+ v) σ) (x + 1) = v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((x + 1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   `() = u` by fs[] >>
           metis_tac[fsatis_def]))
     >- (fs[SUBSET_DEF,IMAGE_DEF,mm2folm_def] >> metis_tac[])
     >- (qexists_tac `x'` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,interpret_def,APPLY_UPDATE_THM,mm2folm_def]
	>- fs[mm2folm_def]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((x + 1 =+ x') σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x''' = x + 1` (* 2 *)
	      >- (rw[APPLY_UPDATE_THM] >> fs[mm2folm_def])
	      >- (rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])) >>
	   `((x + 1 =+ x') σ) (x + 1) = x'` by fs[APPLY_UPDATE_THM] >>
	   `(mm2folm M).domain = M.frame.world` by fs[mm2folm_def] >>
	   metis_tac[]))));





val tvars_def = Define`
  tvars (fVar a) = {a} /\
  tvars (fConst a) = {}`;

val fvars_def = Define`
  fvars (fRrel a t1 t2) = tvars t1 ∪ tvars t2 /\
  fvars (fPrel a t) = tvars t /\
  fvars (fDISJ ff1 ff2) = (fvars ff1) ∪ (fvars ff2) /\
  fvars (fNOT ff) = fvars ff /\
  fvars (fEXISTS n ff) = n INSERT (fvars ff) /\
  fvars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val tconsts_def = Define`
  tconsts (fVar a) = {} /\
  tconsts (fConst a) = {a}`;

val fconsts_def = Define`
  fconsts (fRrel a t1 t2) = tconsts t1 ∪ tconsts t2 /\
  fconsts (fPrel a t) = tconsts t /\
  fconsts (fDISJ ff1 ff2) = (fconsts ff1) ∪ (fconsts ff2) /\
  fconsts (fNOT ff) = fconsts ff /\
  fconsts (fEXISTS n ff) = n INSERT (fconsts ff) /\
  fconsts (fEQ t1 t2) = tconsts t1 ∪ tconsts t2`;


val freevars_def = Define`
  freevars (fRrel a t1 t2) = tvars t1 ∪ tvars t2 /\
  freevars (fPrel a t) = tvars t /\
  freevars (fDISJ ff1 ff2) = freevars ff1 ∪ freevars ff2 /\
  freevars (fNOT ff) = freevars ff /\
  freevars (fEXISTS n ff) = freevars ff DELETE n /\
  freevars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | freevars phi SUBSET {x}}`;

val frealizes_def = Define`
  frealizes M x G <=> ?w. ftype x G /\ w IN M.domain /\
                          !σ phi. (IMAGE σ univ(:num)) SUBSET M.domain /\ phi IN G ==> fsatis M ((x=+w)σ) phi`;



(* 			    
val isLang_def = Define`
  isLang cset phiset <=> !phi. phi IN phiset ==> fconsts phi ⊆ cset`;
*)

val ok_form_def = Define`ok_form M phi <=> fconsts phi ⊆ FDOM M.consts`

(* { phi | ok_form M phi} *)

val consistent_def = Define`
  consistent M G <=>
      !G0. FINITE G0 /\ G0 ⊆ G ==> ?σ. !phi. phi ∈ G0 ==> fsatis M σ phi `;
  
val n_saturated_def = Define`
  n_saturated M n <=>
     !A M' G x.
        FINITE A /\ CARD A <= n /\ A SUBSET M.domain /\
        expansion M A M' /\ G SUBSET { phi | ok_form M' phi} /\
        ftype x G /\ consistent M' G 
         ==>
        frealizes M' x G`;

val countably_saturated_def = Define`
  countably_saturated M <=> !n. n_saturated M n`;
			     
                      


val thm_2_65 = store_thm(
  "thm_2_65",
  ``!M. countably_saturated (mm2folm M) ==> M_sat M``,
  rw[countably_saturated_def,n_saturated_def,M_sat_def] >>
  qabbrev_tac `Σ' = {fRrel u (fConst 0) (fVar x)} UNION (IMAGE (ST x u) Σ)` >>
  qabbrev_tac `MA = <| domain := M.frame.world ;
                       consts := FEMPTY |+ (0,w);
                       fnsyms := \x y. ARB;
		       predsyms := \p w. (w IN M.frame.world /\ M.valt p w);
		       relsyms := \ (u:unit) w1 w2. (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) |>` >>
  `consistent MA Σ'`
      by rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
         Cases_on `(fRrel () (fConst 0) (fVar x)) IN G0` (* 2 *)
	 >- `G0 =  (fRrel () (fConst 0) (fVar x)) INSERT (G0 DELETE (fRrel () (fConst 0) (fVar x)))` by metis_tac[INSERT_DELETE] >>
	    `!f. f IN G0 ==> f = fRrel () (fConst 0) (fVar x) \/ f IN (IMAGE (ST x ()) Σ)`
	       by (rpt strip_tac >>
	          `f <> fRrel () (fConst 0) (fVar x) ==> f ∈ IMAGE (ST x ()) Σ` suffices_by metis_tac[] >>
		  strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
	    qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x () x'}` >>
	    `FINITE ps`
	        by (cheat) >>
            `ps SUBSET Σ` by cheat >>
	    `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	    qexists_tac `\n. x'` >> rw[fsatis_def] (* 2 *)
	    >- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF])
	    >- `IMAGE (λn. x') 𝕌(:num) ⊆ MA.domain` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF]) >>
	       Cases_on `phi = fRrel () (fConst 0) (fVar x)` (* 2 *)
	       >- (fs[] >> rw[feval_def,interpret_def,Abbr`MA`])
	       >- `∃t. phi = ST x () t ∧ t ∈ ps` by cheat >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `() = u` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x u t)` by fs[] >>
		  
	       
	          
	    
	 
