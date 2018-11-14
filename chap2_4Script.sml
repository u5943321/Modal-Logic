open HolKernel Parse boolLib bossLib;
open combinTheory;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

val _ = new_theory "chap2_4";


val _ = Datatype`
	fform = fRrel num num
	       | fVrel 'a num
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ num num`;

val count_fvar_def = Define`
  count_fvar (fRrel n1 n2) = {n1;n2} /\
  count_fvar (fVrel a n) = {n} /\
  count_fvar (fDISJ ff1 ff2) = (count_fvar ff1) ∪ (count_fvar ff2) /\
  count_fvar (fNOT ff) = count_fvar ff /\
  count_fvar (fEXISTS n ff) = n INSERT (count_fvar ff) /\
  count_fvar (fEQ n1 n2) = {n1;n2}`;

val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

val fIMP_def = Define`
  fIMP ff1 ff2 = fDISJ (fNOT ff1) ff2`;

val ST_def = Define`
  (ST x (VAR p) <=> fVrel p x) /\
  (ST x (FALSE) <=> fNOT (fEQ x x)) /\
  (ST x (NOT phi) <=> fNOT (ST x phi)) /\
  (ST x (DISJ phi psi) <=> fDISJ (ST x phi) (ST x psi)) /\
  (ST x (DIAM phi) <=> fEXISTS (x + 1) (fAND (fRrel x (x + 1)) (ST (x + 1) phi)))`;

val feval_def = Define`
  (feval M σ (fVrel p x) <=> M.valt p (σ x)) /\
  (feval M σ (fRrel x y) <=> M.frame.rel (σ x) (σ y)) /\
  (feval M σ (fDISJ ff1 ff2) <=> (feval M σ ff1 \/ feval M σ ff2)) /\
  (feval M σ (fNOT ff) <=> ¬(feval M σ ff)) /\
  (feval M σ (fEXISTS n ff) <=> ?w. w IN M.frame.world /\
                                feval M ((n =+ w)σ) ff) /\
  (feval M σ (fEQ ff1 ff2) <=> ff1 = ff2)`;

val fsatis_def = Define`
  fsatis M σ fform <=> (IMAGE σ univ(:num)) SUBSET M.frame.world /\ feval M σ fform`;

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

