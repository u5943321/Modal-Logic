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



val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;


val prop_2_47_ii = store_thm(
  "prop_2_47_ii",
  ``!phi M. universal_true M phi <=> (!σ. IMAGE σ univ(:num) SUBSET M.frame.world ==> (fsatis (mm2folm M) σ (fFORALL x (ST x u phi))))``,
  rw[universal_true_def,fFORALL_def,fsatis_def,feval_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- fs[mm2folm_def]
  >- (`!x'. x' IN (mm2folm M).domain ==> feval (mm2folm M) ((x =+ x') σ) (ST x () phi)` suffices_by metis_tac[] >> rw[] >>
     `fsatis (mm2folm M) ((x =+ x') σ) (ST x () phi)` suffices_by metis_tac[fsatis_def] >>
     `x' IN M.frame.world` by fs[mm2folm_def] >>
     `satis M x' phi` by metis_tac[] >>
     `IMAGE ((x =+ x') σ) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x''' = x` >> rw[APPLY_UPDATE_THM] >> fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[]) >>
     `((x =+ x') σ) x = x'` by fs[APPLY_UPDATE_THM] >> metis_tac[prop_2_47_i])
  >- (`IMAGE (\n.w) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
     `∀x'.
            x' IN (mm2folm M).domain ==>
            feval (mm2folm M) ((x =+ x') (\n.w)) (ST x () phi)` by metis_tac[] >>
     `w IN (mm2folm M).domain` by fs[mm2folm_def] >>
     `feval (mm2folm M) ((x =+ w) (λn. w)) (ST x () phi)` by metis_tac[] >>
     `IMAGE ((x =+ w) (λn. w)) 𝕌(:num) ⊆ M.frame.world`
         by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` >> rw[APPLY_UPDATE_THM]) >>
     `fsatis (mm2folm M) ((x =+ w) (λn. w)) (ST x () phi)` by metis_tac[fsatis_def] >>
     `((x =+ w) (λn. w)) x = w` by fs[APPLY_UPDATE_THM] >>
     imp_res_tac prop_2_47_i >> metis_tac[]));
     
  


val ST_alt_def = Define`
  (ST_alt x u (VAR p) <=> fPrel p (fVar x)) /\
  (ST_alt x u (FALSE) <=> fNOT (fEQ (fVar x) (fVar x))) /\
  (ST_alt x u (NOT phi) <=> fNOT (ST_alt x u phi)) /\
  (ST_alt x u (DISJ phi psi) <=> fDISJ (ST_alt x u phi) (ST_alt x u psi)) /\
  (ST_alt x u (DIAM phi) <=> fEXISTS (1 - x) (fAND (fRrel u (fVar x) (fVar (1 - x))) (ST_alt (1 - x) u phi)))`;


val prop_2_47_i_alt = store_thm(
  "prop_2_47_i_alt",
  ``!M w:'b phi σ. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ 1) phi <=> fsatis (mm2folm M) σ (ST_alt 1 u phi)) /\
		           (satis M (σ 0) phi <=> fsatis (mm2folm M) σ (ST_alt 0 u phi))``,
  Induct_on `phi` >> rw[] (* 10 *)
  >- (rw[feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- rw[mm2folm_def]
     >- (rw[mm2folm_def,interpret_def] (* 2 *)
        >> metis_tac[satis_def,IN_DEF])
     >- (fs[mm2folm_def,interpret_def] >> rw[satis_def] >> metis_tac[IN_DEF]))
  >- (rw[feval_def,ST_alt_def,fsatis_def,mm2folm_def,interpret_def] >> eq_tac >> rw[] (* 3 *)
     >- metis_tac[satis_def,IN_DEF]
     >- metis_tac[satis_def,IN_DEF]
     >- (rw[satis_def] >> metis_tac[IN_DEF]))
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,interpret_def])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,interpret_def])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,interpret_def])
  >- (fs[satis_def,feval_def,ST_alt_def,fsatis_def,mm2folm_def,interpret_def])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 5 *)
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- fs[]
     >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 5 *)
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- fs[mm2folm_def]
     >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- fs[mm2folm_def]
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- fs[mm2folm_def]
	>- rw[mm2folm_def,interpret_def,APPLY_UPDATE_THM] 
	>- (fs[fsatis_def] >>
           `((0 =+ v) σ) 0 = v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((0 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	       by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	           >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[]))
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `x` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,mm2folm_def,interpret_def,APPLY_UPDATE_THM]
        >- fs[mm2folm_def]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((0 =+ x) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]) >>
	   `((0 =+ x) σ) 0 = x` by fs[APPLY_UPDATE_THM] >>
	   `IMAGE ((0 =+ x) σ) 𝕌(:num) ⊆ (mm2folm M).domain` by fs[mm2folm_def] >>
	   metis_tac[mm2folm_def])))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 4 *)
     >- fs[mm2folm_def]
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] (* 3 *)
        >- fs[mm2folm_def]
	>- rw[mm2folm_def,interpret_def,APPLY_UPDATE_THM] 
        >- (fs[fsatis_def] >>
           `((1 =+ v) σ) 1= v` by rw[APPLY_UPDATE_THM] >>
           `IMAGE ((1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	       by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 1` (* 2 *)
	          >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
           metis_tac[]))
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `x` >> rw[] (* 3 *)
        >- fs[feval_def,fAND_def,fsatis_def,mm2folm_def,interpret_def,APPLY_UPDATE_THM]
        >- fs[mm2folm_def]
        >- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((1 =+ x) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF,mm2folm_def] >> metis_tac[]) >>
	   `((1 =+ x) σ) 1 = x` by fs[APPLY_UPDATE_THM] >>
	   `IMAGE ((1 =+ x) σ) 𝕌(:num) ⊆ (mm2folm M).domain` by fs[mm2folm_def] >>
	   metis_tac[mm2folm_def]))));


val ST_alt_two_var = store_thm(
  "ST_alt_two_var",
  ``!phi. fvars (ST_alt 0 u phi) SUBSET {0;1} /\ fvars (ST_alt 1 u phi) SUBSET {0;1}``,
  Induct_on `phi` >> rw[] >> fs[ST_alt_def,fvars_def,SUBSET_DEF,tvars_def] >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >> fs[fAND_def,fvars_def,tvars_def]);






val fequiv_def = Define`
  fequiv (μ:'b itself) ff1 ff2 <=> (!M (σ:num -> 'b). (IMAGE σ univ(:num)) SUBSET M.frame.world
                                                        ==> (fsatis (mm2folm M) σ ff1 <=> fsatis (mm2folm M) σ ff2))`;



val ST_ST_alt_fequiv = store_thm(
  "ST_ST_alt_fequiv",
  ``!phi. fequiv μ (ST 0 u phi) (ST_alt 0 u phi) /\ fequiv μ (ST 1 u phi) (ST_alt 1 u phi)``,
  rw[ST_alt_def,ST_def,fequiv_def] (* 2 *)
  >- (eq_tac >> rw[] (* 2 *)
     >- (`satis M (σ 0) phi` by metis_tac[prop_2_47_i] >>
        metis_tac[prop_2_47_i_alt])
     >- metis_tac[prop_2_47_i_alt,prop_2_47_i])
  >- metis_tac[prop_2_47_i,prop_2_47_i_alt]);




  
val prop_2_49_i = store_thm(
  "prop_2_49_i",
  ``!phi. ?fphi. (fvars fphi) SUBSET {0;1} /\
                 fequiv μ (ST 0 u phi) fphi``,
  rw[] >> qexists_tac `(ST_alt 0 u phi)` >>
  `u = ()` by fs[] >>
  metis_tac[ST_alt_two_var,ST_ST_alt_fequiv]);





val tconsts_def = Define`
  tconsts (fVar a) = {} /\
  tconsts (fConst a) = {a}`;

val fconsts_def = Define`
  fconsts (fRrel a t1 t2) = tconsts t1 ∪ tconsts t2 /\
  fconsts (fPrel a t) = tconsts t /\
  fconsts (fDISJ ff1 ff2) = (fconsts ff1) ∪ (fconsts ff2) /\
  fconsts (fNOT ff) = fconsts ff /\
  fconsts (fEXISTS n ff) = fconsts ff /\
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


val no_constant_fsatis_lemma = store_thm(
  "no_constant_fsatis_lemma",
  ``!M1 M2. (M1.domain = M2.domain /\
            M1.predsyms = M2.predsyms /\
	    M1.relsyms = M2.relsyms)
            ==> !phi. fconsts phi = {} ==> !σ. IMAGE σ univ(:num) SUBSET M1.domain ==>
            fsatis M1 σ phi = fsatis M2 σ phi``,
  strip_tac >> strip_tac >> strip_tac >> 
  Induct_on `phi` >> rw[fsatis_def,feval_def] (* 6 *)
  >- (Cases_on `f` >> rw[] (* 2 *)
     >- (Cases_on `f0` >> rw[] (* 2 *)
        >- fs[interpret_def]
	>- fs[fconsts_def,tconsts_def])
     >- fs[fconsts_def,tconsts_def])
  >- (Cases_on `f` >> rw[] (* 2 *)
     >- fs[interpret_def]
     >- fs[fconsts_def,tconsts_def])
  >- (fs[fconsts_def] >> metis_tac[fsatis_def])
  >- (fs[fconsts_def] >> metis_tac[fsatis_def])
  >- (fs[fconsts_def,fsatis_def] >> rw[EQ_IMP_THM] (* 2 same *)
     >- (qexists_tac `x` >> rw[] >>
        `IMAGE ((n =+ x) σ) 𝕌(:num) ⊆ M1.domain` suffices_by metis_tac[] >>
	rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> rw[] (* 2 *)
	>- fs[APPLY_UPDATE_THM]
	>- (fs[APPLY_UPDATE_THM,IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
     >- (qexists_tac `x` >> rw[] >>
        `IMAGE ((n =+ x) σ) 𝕌(:num) ⊆ M1.domain` suffices_by metis_tac[] >>
	rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> rw[] (* 2 *)
	>- fs[APPLY_UPDATE_THM]
	>- (fs[APPLY_UPDATE_THM,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])))
  >- (fs[fconsts_def] >> Cases_on `f` >> rw[] (* 2 *)
     >- (Cases_on `f0` >> rw[] (* 2 *)
        >- fs[interpret_def]
	>- fs[tconsts_def])
     >- fs[tconsts_def]));

val ST_no_constant = store_thm(
  "ST_no_constant",
  ``!f x u. fconsts (ST x u f) = {}``,
  Induct_on `f` >> rw[ST_def,fconsts_def,tconsts_def] (* 5 *) >>
  `() = u` by fs[] >> fs[fAND_def,fconsts_def,tconsts_def,ST_def]);
  
                      
val ST_one_freevar = store_thm(
  "ST_one_freevar",
  ``!f x u. freevars (ST x u f) SUBSET {x}``,
  Induct_on `f` >> rw[ST_def,freevars_def,fvars_def,tvars_def,fAND_def] >>
  `(freevars (ST (x + 1) () f)) SUBSET {x + 1}` by metis_tac[] >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> metis_tac[]);


val diff_form_diff_ST = store_thm(
  "diff_form_diff_ST",
  ``!f1 f2. f1 <> f2 ==> !x u. ST x u f1 <> ST x u f2``,
  Induct_on `f1` >> rw[] (* 5 *)
  >- (Cases_on `f2` >> rw[ST_def])
  >- (Cases_on `f2` >> rw[ST_def] (* 2 *) >>
     `() = u` by fs[] >> metis_tac[])
  >- (Cases_on `f2` >> rw[ST_def] >> Cases_on `f` >> fs[ST_def])
  >- (Cases_on `f2` >> rw[ST_def] >> Cases_on `f1` >> fs[ST_def])
  >- (Cases_on `f2` >> rw[ST_def,fAND_def] >> metis_tac[]));
  
  
val ST_INJ_univ = store_thm(
  "ST_INJ_univ",
  ``∀x u. INJ (ST x u) 𝕌(:α form) 𝕌(:(α, unit) fform)``,
  rw[INJ_DEF] >> metis_tac[diff_form_diff_ST]);


val ST_INJ = store_thm(
  "ST_INJ",
  ``!x u s1 s2. (!f. f IN s1 ==> (ST x u f) IN s2) ==> INJ (ST x u) s1 s2``,
  rw[INJ_DEF] >> metis_tac[diff_form_diff_ST]);


  

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
      by (rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
         Cases_on `(fRrel () (fConst 0) (fVar x)) IN G0` (* 2 *)
	 >- (`G0 =  (fRrel () (fConst 0) (fVar x)) INSERT (G0 DELETE (fRrel () (fConst 0) (fVar x)))` by metis_tac[INSERT_DELETE] >>
	    `!f. f IN G0 ==> f = fRrel () (fConst 0) (fVar x) \/ f IN (IMAGE (ST x ()) Σ)`
	       by (rpt strip_tac >>
	          `f <> fRrel () (fConst 0) (fVar x) ==> f ∈ IMAGE (ST x ()) Σ` suffices_by metis_tac[] >>
		  strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
	    qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x () x'}` >>
            `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	    `FINITE ps` 
	        by (`(IMAGE (ST x ()) ps) SUBSET G0`
		       by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	           `INJ (ST x ()) ps G0`
	               by (irule ST_INJ >> rw[Abbr`ps`]) >>
		   SPOSE_NOT_THEN ASSUME_TAC >>
		   metis_tac[INFINITE_INJ]) >>
	    `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	    qexists_tac `\n. x'` >> rw[fsatis_def] (* 2 *)
	    >- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF])
	    >- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.domain` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF]) >>
	       Cases_on `phi = fRrel () (fConst 0) (fVar x)` (* 2 *)
	       >- (fs[] >> rw[feval_def,interpret_def,Abbr`MA`])
	       >- (`∃t. phi = ST x () t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `() = u` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x u t)` by fs[] >>
		  `fconsts (ST x u t) = {}` by metis_tac[ST_no_constant] >>
		  `(mm2folm M).domain = MA.domain` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).predsyms = MA.predsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).relsyms = MA.relsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[no_constant_fsatis_lemma] >>
		  fs[fsatis_def])))
	  >-  (`!f. f IN G0 ==> f IN (IMAGE (ST x ()) Σ)`
	       by (rpt strip_tac >>
	          `f IN Σ'` by fs[SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
	          >- fs[] >- metis_tac[]) >>
	       fs[satisfiable_in_def] >>
	       qabbrev_tac `ps = {x' | x' IN Σ /\ ?f. f IN G0 /\ f = ST x () x'}` >>
               `ps SUBSET Σ` by fs[Abbr`ps`,SUBSET_DEF] >>
	       `FINITE ps` 
	           by (`(IMAGE (ST x ()) ps) SUBSET G0`
		           by (fs[Abbr`ps`,SUBSET_DEF] >> metis_tac[]) >>
	               `INJ (ST x ()) ps G0`
	                   by (irule ST_INJ >> rw[Abbr`ps`]) >>
		        SPOSE_NOT_THEN ASSUME_TAC >>
		        metis_tac[INFINITE_INJ]) >>
	       `∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧ ∀form. form ∈ ps ⇒ satis M x form` by metis_tac[] >>
	        qexists_tac `\n. x'` >> rw[fsatis_def] (* 2 *)
		>- (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF])
		>- (`IMAGE (λn. x') 𝕌(:num) ⊆ MA.domain` by (rw[Abbr`MA`] >> rw[IMAGE_DEF,SUBSET_DEF]) >>
		   `∃t. phi = ST x () t ∧ t ∈ ps`
	               by (`phi IN Σ'` by fs[SUBSET_DEF] >>
		          fs[Abbr`ps`,Abbr`Σ'`]
			  >- fs[] >- metis_tac[]) >>
	          `satis M x' t` by metis_tac[] >>
		  `(λn. x') x = x'` by fs[] >>
		  `() = u` by fs[] >>
		  `IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world` by fs[Abbr`MA`] >>
		  imp_res_tac prop_2_47_i >>
		  `satis M ((λn. x') x) t` by metis_tac[] >>
                  `fsatis (mm2folm M) (λn. x') (ST x u t)` by fs[] >>
		  `fconsts (ST x u t) = {}` by metis_tac[ST_no_constant] >>
		  `(mm2folm M).domain = MA.domain` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).predsyms = MA.predsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `(mm2folm M).relsyms = MA.relsyms` by fs[mm2folm_def,Abbr`MA`] >>
		  `fsatis MA (λn. x') phi` by metis_tac[no_constant_fsatis_lemma] >>
		  fs[fsatis_def]))) >>
   `FINITE {w}` by fs[] >>
   `CARD {w} <= 1` by fs[] >>
   `{w} SUBSET (mm2folm M).domain` by fs[SUBSET_DEF,mm2folm_def] >>
   `expansion (mm2folm M) {w} MA`
       by (rw[expansion_def] >> map_every qexists_tac [`{0}`,`\n.w`] >> rw[] (* 3 *)
          >- fs[mm2folm_def]
	  >- fs[BIJ_DEF,INJ_DEF,SURJ_DEF]
	  >- (fs[Abbr`MA`,mm2folm_def] >> rw[fmap_EXT] >> `FINITE {0}` by fs[] >> fs[FUN_FMAP_DEF])) >>
   `Σ' SUBSET {phi |ok_form MA phi}`
       by (rw[SUBSET_DEF,ok_form_def,Abbr`MA`] >>
          fs[Abbr`Σ'`] (* 2 *)
	  >- (`fconsts (fRrel () (fConst 0) (fVar x)) = {0}` by fs[fconsts_def,tconsts_def] >>
	     `fconsts x' = {0}` by metis_tac[] >> fs[])
	  >- (`fconsts (ST x () x''') = {}` by metis_tac[ST_no_constant] >>
	     `fconsts x' = {}` by metis_tac[] >> metis_tac[NOT_IN_EMPTY])) >>
   `ftype x Σ'`
       by (rw[ftype_def,SUBSET_DEF] >> fs[Abbr`Σ'`] (* 2 *)
          >- (`freevars (fRrel () (fConst 0) (fVar x)) = {x}`
	         by rw[freevars_def,tvars_def] >>
	     `x'' IN {x}` by metis_tac[] >> fs[])
	  >- (`freevars (ST x () x''') SUBSET {x}` by metis_tac[ST_one_freevar] >>
	     `x'' IN {x}` by metis_tac[SUBSET_DEF] >> fs[])) >>
   `frealizes MA x Σ'` by metis_tac[] >>
   fs[frealizes_def] >>
   rw[satisfiable_in_def] (* 2 *)
   >- rw[SUBSET_DEF]
   >- (qexists_tac `w'` >> rw[] (* 3 *)
      >- fs[Abbr`MA`]
      >- (`(fRrel () (fConst 0) (fVar x)) IN Σ'` by fs[Abbr`Σ'`] >>
         `IMAGE (\n. w') univ(:num) SUBSET MA.domain`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
	 `fsatis MA ((x =+ w') (λn. w')) (fRrel () (fConst 0) (fVar x))` by metis_tac[] >>
	 fs[fsatis_def,feval_def,APPLY_UPDATE_THM,interpret_def,Abbr`MA`])
      >- (`IMAGE (\n. w') univ(:num) SUBSET MA.domain`
	     by fs[SUBSET_DEF,IMAGE_DEF,Abbr`MA`,mm2folm_def] >>
	 `(ST x () form) IN Σ'` by fs[Abbr`Σ'`] >>
	 `fsatis MA ((x =+ w') (λn. w')) (ST x () form)` by metis_tac[] >>
	 `(IMAGE ((x =+ w') (λn. w')) univ(:num)) SUBSET M.frame.world`
	     by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x` (* 2 *) >> rw[] >>
	         fs[APPLY_UPDATE_THM,Abbr`MA`]) >>
	 `fconsts (ST x u form) = ∅` by metis_tac[ST_no_constant] >>
	 `fsatis (mm2folm M) ((x =+ w') (λn. w')) (ST x () form)`
	     by (`u = ()` by fs[] >>
	        `(mm2folm M).domain = MA.domain /\ (mm2folm M).predsyms = MA.predsyms /\
		(mm2folm M).relsyms = MA.relsyms` by fs[Abbr`MA`,mm2folm_def] >>
		`IMAGE ((x =+ w') (λn. w')) 𝕌(:num) ⊆ MA.domain` by fs[Abbr`MA`] >>
		metis_tac[no_constant_fsatis_lemma]) >>
	 `(x =+ w') (λn. w') x = w'` by fs[APPLY_UPDATE_THM] >>
	 metis_tac[prop_2_47_i])));
	     
		  
		  
val invariant_for_bisim_def = Define`
  invariant_for_bisim (a:'a itself) (b:'b itself) ff x <=> freevars ff SUBSET {x} /\
                               !M N w v. bisim_world M N (w:'a) (v:'b) ==>
			       (!σ1 σ2.
			        IMAGE σ1 univ(:num) SUBSET M.frame.world /\
				IMAGE σ2 univ(:num) SUBSET N.frame.world ==>
                                (fsatis (mm2folm M) ((x =+ w)σ1) ff <=> fsatis (mm2folm N) ((x =+ v)σ2) ff))`;

val thm_2_68 = store_thm(
  "thm_2_68",
  ``
	          
	    
	 
