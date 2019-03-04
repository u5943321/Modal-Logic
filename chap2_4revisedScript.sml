open HolKernel Parse boolLib bossLib;
open combinTheory;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open finite_mapTheory;
open chap1Theory;


val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_4revised";

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
	       | fConst num (fterm list) ;
	fform = fRrel 'r fterm fterm
	       | fPrel 'p fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`; 

val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;


val fIMP_def = Define`
  fIMP ff1 ff2 = fDISJ (fNOT ff1) ff2`;


val tvars_def = Define`
  tvars (fVar a) = {a} /\
  tvars (fConst a l) = {}`;

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



(*
		  
		  
val invariant_for_bisim_def = Define`
  invariant_for_bisim (a:'a itself) (b:'b itself) ff x <=> freevars ff SUBSET {x} /\
                               !M N w v. bisim_world M N (w:'a) (v:'b) ==>
			       (!σ1 σ2.
			        IMAGE σ1 univ(:num) SUBSET M.frame.world /\
				IMAGE σ2 univ(:num) SUBSET N.frame.world ==>
                                (fsatis (mm2folm M) ((x =+ w)σ1) ff <=> fsatis (mm2folm N) ((x =+ v)σ2) ff))`;

val thm_2_68 = store_thm(
  "thm_2_68",


*)


val _ = export_theory();
	          
	    
	 
