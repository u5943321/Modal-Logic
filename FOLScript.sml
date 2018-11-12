
open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOL";

val _ = Datatype`
	fform = fRrel num num
	       | fVrel 'a num
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ num num`;

val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

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

val prop_2_47_ii = store_thm(
  "prop_2_47_ii",
  ``!M phi σ x. (universal_true M phi <=> !w. ?x. σ x = w /\ )

val fequiv_def = Define`
  fequiv (μ:tyi itself) ff1 ff2 <=> !M u:tyi σ. feval M σ 



val prop_2_49_i = store_thm(
  "prop_2_49_i",
  ``!phi. ?fphi. feval M σ 

val _ = export_theory();

