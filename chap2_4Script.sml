open HolKernel Parse boolLib bossLib;
open combinTheory;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

val _ = new_theory "chap2_4";



val _ = Datatype`
        fterm = fVar num
	       | fConst num ;
	fform = fRrel fterm fterm
	       | fVrel 'a fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`;





val tvars_def = Define`
  tvars (fVar a) = {a} /\
  tvars (fConst a) = {}`;

val fvars_def = Define`
  fvars (fRrel t1 t2) = tvars t1 ∪ tvars t2 /\
  fvars (fVrel a t) = tvars t /\
  fvars (fDISJ ff1 ff2) = (fvars ff1) ∪ (fvars ff2) /\
  fvars (fNOT ff) = fvars ff /\
  fvars (fEXISTS n ff) = n INSERT (fvars ff) /\
  fvars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val tconsts_def = Define`
  tconsts (fVar a) = {} /\
  tconsts (fConst a) = {a}`;

val fconsts_def = Define`
  fconsts (fRrel t1 t2) = tconsts t1 ∪ tconsts t2 /\
  fconsts (fVrel a t) = tconsts t /\
  fconsts (fDISJ ff1 ff2) = (fconsts ff1) ∪ (fconsts ff2) /\
  fconsts (fNOT ff) = fconsts ff /\
  fconsts (fEXISTS n ff) = n INSERT (fconsts ff) /\
  fconsts (fEQ t1 t2) = tconsts t1 ∪ tconsts t2`;


val freevars_def = Define`
  freevars (fRrel t1 t2) = tvars t1 ∪ tvars t2 /\
  freevars (fVrel a t) = tvars t /\
  freevars (fDISJ ff1 ff2) = freevars ff1 ∪ freevars ff2 /\
  freevars (fNOT ff) = freevars ff /\
  freevars (fEXISTS n ff) = freevars ff DELETE n /\
  freevars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

val fIMP_def = Define`
  fIMP ff1 ff2 = fDISJ (fNOT ff1) ff2`;

val ST_def = Define`
  (ST x (VAR p) <=> fVrel p (fVar x)) /\
  (ST x (FALSE) <=> fNOT (fEQ (fVar x) (fVar x))) /\
  (ST x (NOT phi) <=> fNOT (ST x phi)) /\
  (ST x (DISJ phi psi) <=> fDISJ (ST x phi) (ST x psi)) /\
  (ST x (DIAM phi) <=> fEXISTS (x + 1) (fAND (fRrel (fVar x) (fVar (x + 1))) (ST (x + 1) phi)))`;

val fteval_def = Define`
  fteval σ c (fVar n) = σ n /\
  fteval σ c (fConst n) = c n`;
  
val feval_def = Define`
  (feval M c σ (fVrel p t) <=> M.valt p (fteval σ c t)) /\
  (feval M c σ (fRrel t1 t2) <=> M.frame.rel (fteval σ c t1) (fteval σ c t2)) /\
  (feval M c σ (fDISJ ff1 ff2) <=> (feval M c σ ff1 \/ feval M c σ ff2)) /\
  (feval M c σ (fNOT ff) <=> ¬(feval M c σ ff)) /\
  (feval M c σ (fEXISTS n ff) <=> ?w. w IN M.frame.world /\
                                feval M c ((n =+ w)σ) ff) /\
  (feval M c σ (fEQ t1 t2) <=> fteval σ c t1 = fteval σ c t2)`;

val fsatis_def = Define`
  fsatis M c σ fform <=> (IMAGE σ univ(:num)) SUBSET M.frame.world /\
                         (IMAGE c univ(:num)) SUBSET M.frame.world /\
                         feval M c σ fform`;

val fsatis_AND = store_thm(
  "fsatis_AND",
  ``!σ ff1 ff2 M. (fsatis M σ (fAND ff1 ff2) <=> (fsatis M σ ff1 /\ fsatis M σ ff2))``,
  rw[fsatis_def,fAND_def,feval_def] >> metis_tac[]);

val fsatis_fFORALL = store_thm(
  "fsatis_fFORALL",
  ``!σ ff M. (IMAGE σ univ(:num)) SUBSET M.frame.world
               ==> (fsatis M σ (fFORALL n ff) <=> !w. w IN M.frame.world ==> fsatis M ((n =+ w)σ) ff)``,
  rw[fFORALL_def,fsatis_def,feval_def,APPLY_UPDATE_THM] >> eq_tac >> rw[]
  >- (fs[IMAGE_DEF,SUBSET_DEF] >> rw[] >> Cases_on `x' = n` >> rw[APPLY_UPDATE_THM] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]);

val fsatis_fIMP = store_thm(
  "fsatis_fIMP",
  ``!σ ff1 ff2 M. (IMAGE σ univ(:num)) SUBSET M.frame.world
                    ==> (fsatis M σ (fIMP ff1 ff2) <=> (fsatis M σ ff1 ==> fsatis M σ ff2))``,
  rw[fIMP_def,fsatis_def,feval_def] >> metis_tac[]);

     

val prop_2_47_i = store_thm(
  "prop_2_47_i",
  ``!M w:'b phi σ x. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ x) phi <=> fsatis M σ (ST x phi))``,
  Induct_on `phi` >> rw[]
  >- (rw[feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 2 *)
     >- metis_tac[satis_def,IN_DEF]
     >- (rw[satis_def] >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
                       >- metis_tac[IN_DEF]))
  >- (rw[satis_def,feval_def,ST_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] >> fs[fsatis_def] >>
        `((x + 1 =+ v) σ) (x + 1) = v` by rw[APPLY_UPDATE_THM] >>
        `IMAGE ((x + 1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	metis_tac[])
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `((x + 1 =+ w) σ) (x + 1)` >> rw[] (* 3 *)
        >- (fs[feval_def,fAND_def,fsatis_def] >>
	   `((x + 1 =+ w) σ x) = σ x` by rw[APPLY_UPDATE_THM] >>
	   `IMAGE ((x + 1 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[])
	>- (fs[feval_def,fAND_def] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((x + 1 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = x + 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[]))));


val ST_alt_def = Define`
  (ST_alt x (VAR p) <=> fVrel p x) /\
  (ST_alt x (FALSE) <=> fNOT (fEQ x x)) /\
  (ST_alt x (NOT phi) <=> fNOT (ST_alt x phi)) /\
  (ST_alt x (DISJ phi psi) <=> fDISJ (ST_alt x phi) (ST_alt x psi)) /\
  (ST_alt x (DIAM phi) <=> fEXISTS (1 - x) (fAND (fRrel x (1 - x)) (ST_alt (1 - x) phi)))`;


val prop_2_47_i_alt = store_thm(
  "prop_2_47_i_alt",
  ``!M w:'b phi σ. (IMAGE σ univ(:num)) SUBSET M.frame.world
                       ==> (satis M (σ 1) phi <=> fsatis M σ (ST_alt 1 phi)) /\
		           (satis M (σ 0) phi <=> fsatis M σ (ST_alt 0 phi))``,
  Induct_on `phi` >> rw[] (* 10 *)
  >- (rw[feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 2 *)
     >- metis_tac[satis_def,IN_DEF]
     >- (rw[satis_def] >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
                       >- metis_tac[IN_DEF]))
  >- (rw[feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 2 *)
     >- metis_tac[satis_def,IN_DEF]
     >- (rw[satis_def] >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
                       >- metis_tac[IN_DEF]))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] >> fs[fsatis_def] >>
        `((0 =+ v) σ) 0 = v` by rw[APPLY_UPDATE_THM] >>
        `IMAGE ((0 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	metis_tac[])
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `((0 =+ w) σ) 0` >> rw[] (* 3 *)
        >- (fs[feval_def,fAND_def,fsatis_def] >>
	   `(0 =+ w) σ 0 = w` by rw[APPLY_UPDATE_THM] >>
	   `IMAGE ((0 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   fs[APPLY_UPDATE_THM])
        >- fs[APPLY_UPDATE_THM]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((0 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 0` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[])))
  >- (rw[satis_def,feval_def,ST_alt_def,fsatis_def] >> eq_tac >> rw[] (* 3 *)
     >- (qexists_tac `v` >> rw[fAND_def,feval_def,APPLY_UPDATE_THM] >> fs[fsatis_def] >>
        `((1 =+ v) σ) 1= v` by rw[APPLY_UPDATE_THM] >>
        `IMAGE ((1 =+ v) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	metis_tac[])
     >- (fs[SUBSET_DEF,IMAGE_DEF] >> metis_tac[])
     >- (qexists_tac `((1 =+ w) σ) 1` >> rw[] (* 3 *)
        >- (fs[feval_def,fAND_def,fsatis_def] >>
	   `(1 =+ w) σ 1 = w` by rw[APPLY_UPDATE_THM] >>
	   `IMAGE ((1 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   fs[APPLY_UPDATE_THM])
        >- fs[APPLY_UPDATE_THM]
	>- (fs[feval_def,fAND_def,fsatis_def] >>
	   `IMAGE ((1 =+ w) σ) 𝕌(:num) ⊆ M.frame.world`
	   by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = 1` (* 2 *)
	      >> rw[APPLY_UPDATE_THM] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	   metis_tac[]))));

val ST_alt_two_var = store_thm(
  "ST_alt_two_var",
  ``!phi. count_fvar (ST_alt 0 phi) SUBSET {0;1} /\ count_fvar (ST_alt 1 phi) SUBSET {0;1}``,
  Induct_on `phi` >> rw[] >> fs[ST_alt_def,count_fvar_def,SUBSET_DEF] >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >> fs[fAND_def,count_fvar_def]);


val fequiv_def = Define`
  fequiv (μ:'b itself) ff1 ff2 <=> (!M (σ:num -> 'b). (IMAGE σ univ(:num)) SUBSET M.frame.world
                                                        ==> (fsatis M σ ff1 <=> fsatis M σ ff2))`;

val ST_ST_alt_fequiv = store_thm(
  "ST_ST_alt_fequiv",
  ``!phi. fequiv μ (ST 0 phi) (ST_alt 0 phi) /\ fequiv μ (ST 1 phi) (ST_alt 1 phi)``,
  rw[ST_alt_def,ST_def,fequiv_def] (* 2 *)
  >- (eq_tac >> rw[] (* 2 *)
     >- (`satis M (σ 0) phi` by metis_tac[prop_2_47_i] >>
        metis_tac[prop_2_47_i_alt])
     >- metis_tac[prop_2_47_i_alt,prop_2_47_i])
  >- metis_tac[prop_2_47_i,prop_2_47_i_alt]);
  
val prop_2_49_i = store_thm(
  "prop_2_49_i",
  ``!phi. ?fphi. (count_fvar fphi) SUBSET {0;1} /\
                 fequiv μ (ST 0 phi) fphi``,
  rw[] >> qexists_tac `(ST_alt 0 phi)` >> metis_tac[ST_alt_two_var,ST_ST_alt_fequiv]);


val _ = export_theory();

