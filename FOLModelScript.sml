open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory relationTheory arithmeticTheory set_relationTheory
     numpairTheory nlistTheory listTheory rich_listTheory;
open FOLSyntaxTheory;

val _ = ParseExtras.tight_equality()


val _ = new_theory "FOLModel";


val _ = Datatype`
        folmodel = <| dom : 'a set ;
                      fnsyms : num -> 'a list -> 'a;
                      predsyms : num -> 'a -> bool;
                      relsyms : num -> 'a -> 'a -> bool;
                      |>`;

val interpret_def = tDefine "interpret" `
  interpret M σ (V n) = σ n /\
  interpret M σ (Fn f l) = M.fnsyms f (MAP (interpret M σ) l)`
 (WF_REL_TAC `measure (fterm_size o SND o SND)` >> rw[] >> drule tsize_lemma >> rw[])


val feval_def = Define`
  feval M σ (fP p t) = M.predsyms p (interpret M σ t) /\
  feval M σ (fR n t1 t2) = M.relsyms n (interpret M σ t1) (interpret M σ t2) /\
  feval M σ (fIMP f1 f2) = (feval M σ f1 ==> feval M σ f2) /\
  feval M σ (fFALSE) = F /\
  feval M σ (fEXISTS n f) = (?x. x IN M.dom /\ feval M ((n=+x)σ) f) /\
  feval M σ (fFORALL n f) = (!x. x IN M.dom ==> feval M ((n=+x)σ) f)`;



val fsatis_def = Define`
  fsatis M σ fform <=> (IMAGE σ univ(:num)) SUBSET M.dom /\
                       feval M σ fform`;


Theorem interpret_tfvs :
  !M σ1 t σ2. (!n. n IN (tfvs t) ==> σ1 n = σ2 n) ==> interpret M σ1 t = interpret M σ2 t
Proof
  ho_match_mp_tac (theorem "interpret_ind") >> rw[tfvs_def,interpret_def] >> AP_TERM_TAC >> irule MAP_CONG
  >> rw[] >> first_x_assum irule >> rw[] >> fs[PULL_EXISTS,MEM_MAP] >> metis_tac[]
QED


Theorem feval_ffvs :
  !M σ1 σ2 f. (!n. n IN (ffvs f) ==> σ1 n = σ2 n) ==> feval M σ1 f = feval M σ2 f
Proof
  Induct_on `f` >> rw[feval_def,ffvs_def]
  >- metis_tac[interpret_tfvs]
  >- metis_tac[interpret_tfvs]
  >- metis_tac[interpret_tfvs]
  >> (`∀m x. m ∈ ffvs f ==> σ1(|n |-> x|) m = σ2(|n|->x|) m` suffices_by metis_tac[] >>
     rw[APPLY_UPDATE_THM]) 
QED


Theorem interpret_tsubst :
  !v t M σ. (interpret M σ (tsubst v t)) = (interpret M (interpret M σ o v) t)
Proof
  ho_match_mp_tac tsubst_ind >> rw[tsubst_def,interpret_def] 
  >> simp[MAP_MAP_o,combinTheory.o_ABS_R] >> AP_TERM_TAC >> irule MAP_CONG >> rw[]
QED


Theorem VARIANT_NOTIN :
  !s. FINITE s /\ s <> {}  ==> (VARIANT s) NOTIN s
Proof
  rw[VARIANT_def] >> drule MAX_SET_DEF >> rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
  first_x_assum (qspec_then `MAX_SET s + 1` mp_tac) >> fs[]
QED




Theorem feval_fsubst :
  !f v M σ. feval M σ (fsubst v f) = feval M (interpret M σ o v) f
Proof
  Induct_on `f` >> rw[feval_def,tsubst_def,fsubst_def,interpret_tsubst] (* 4 *)
  >- (rw[EQ_IMP_THM] (* 2 *)
     >- (first_x_assum drule >> qmatch_abbrev_tac `feval M s1 f ==> feval M s2 f` >>
        `feval M s1 f <=> feval M s2 f`  suffices_by simp[] >> irule feval_ffvs >>
        simp[Abbr`s1`,Abbr`s2`] >> rw[] >> Cases_on `n' = n` >> fs[APPLY_UPDATE_THM] (* 2 *)
	>- (fs[ffvs_def,tfvs_def] >> simp[interpret_def] >> fs[APPLY_UPDATE_THM])
	>- (fs[ffvs_def,tfvs_def] >> Cases_on `v n'` >> fs[interpret_def] (* 2 *)
	   >- (Cases_on `n'' = VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f))` >> fs[APPLY_UPDATE_THM] >> 
              `¬(n = y)` by fs[] >> fs[] >>
	      `FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f))` by metis_tac[ffvs_FINITE] >>
              `FINITE (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)))` by metis_tac[ffvs_fsubst] >>
	      qabbrev_tac `r = (VARIANT (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))))` >>
	      `r IN (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)))` by
	        (rw[IMAGE_DEF,PULL_EXISTS] >> qexists_tac `n'` >> rw[] >> fs[APPLY_UPDATE_THM,tfvs_def,Abbr`r`,ffvs_fsubst]) >>
              `VARIANT (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))) IN
	       BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` by rw[Abbr`r`] >>
	      `BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)) <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
	      metis_tac[VARIANT_NOTIN])
           >- (`¬(n = y)` by fs[] >> fs[] >> AP_TERM_TAC >> irule LIST_EQ >> rw[EL_MAP] >> 
               irule interpret_tfvs >> rw[] >>
	       Cases_on `n''' = VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f))` >> fs[APPLY_UPDATE_THM] >>
	       `tfvs (EL x' l) ⊆ ffvs (fsubst v⦇n ↦ V n⦈ f)` by
		 (rw[ffvs_fsubst,SUBSET_DEF,PULL_EXISTS] >> qexists_tac `n'` >> rw[] >>
		  fs[APPLY_UPDATE_THM,tfvs_def] >> qexists_tac `tfvs (EL x' l)` >> rw[MEM_MAP] >>
		  qexists_tac `EL x' l` >> rw[EL_MEM]) >>
	       `VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) IN (ffvs (fsubst v⦇n ↦ V n⦈ f))` by metis_tac[SUBSET_DEF] >>
	       `(ffvs (fsubst v⦇n ↦ V n⦈ f)) <> {} /\ FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f))` suffices_by metis_tac[VARIANT_NOTIN] >> rw[ffvs_FINITE] >> metis_tac[MEMBER_NOT_EMPTY,SUBSET_DEF])))
     >- (first_x_assum drule >> qmatch_abbrev_tac `feval M s2 f ==> feval M s1 f` >>
        `feval M s1 f <=> feval M s2 f`  suffices_by simp[] >> irule feval_ffvs >>
        simp[Abbr`s1`,Abbr`s2`] >> rw[] >> Cases_on `n' = n` >> fs[APPLY_UPDATE_THM] (* 2 *)
	>- (fs[ffvs_def,tfvs_def] >> simp[interpret_def] >> fs[APPLY_UPDATE_THM])
	>- (fs[ffvs_def,tfvs_def] >> Cases_on `v n'` >> fs[interpret_def] (* 2 *)
	   >- (Cases_on `n'' = VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f))` >> fs[APPLY_UPDATE_THM] >> 
              `¬(n = y)` by fs[] >> fs[] >>
	      `FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f))` by metis_tac[ffvs_FINITE] >>
              `FINITE (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)))` by metis_tac[ffvs_fsubst] >>
	      qabbrev_tac `r = (VARIANT (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))))` >>
	      `r IN (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)))` by
	        (rw[IMAGE_DEF,PULL_EXISTS] >> qexists_tac `n'` >> rw[] >> fs[APPLY_UPDATE_THM,tfvs_def,Abbr`r`,ffvs_fsubst]) >>
              `VARIANT (BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))) IN
	       BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` by rw[Abbr`r`] >>
	      `BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f)) <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
	      metis_tac[VARIANT_NOTIN])
           >- (`¬(n = y)` by fs[] >> fs[] >> AP_TERM_TAC >> irule LIST_EQ >> rw[EL_MAP] >> 
               irule interpret_tfvs >> rw[] >>
	       Cases_on `n''' = VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f))` >> fs[APPLY_UPDATE_THM] >>
	       `tfvs (EL x' l) ⊆ ffvs (fsubst v⦇n ↦ V n⦈ f)` by
		 (rw[ffvs_fsubst,SUBSET_DEF,PULL_EXISTS] >> qexists_tac `n'` >> rw[] >>
		  fs[APPLY_UPDATE_THM,tfvs_def] >> qexists_tac `tfvs (EL x' l)` >> rw[MEM_MAP] >>
		  qexists_tac `EL x' l` >> rw[EL_MEM]) >>
	       `VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) IN (ffvs (fsubst v⦇n ↦ V n⦈ f))` by metis_tac[SUBSET_DEF] >>
	       `(ffvs (fsubst v⦇n ↦ V n⦈ f)) <> {} /\ FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f))` suffices_by metis_tac[VARIANT_NOTIN] >> rw[ffvs_FINITE] >> metis_tac[MEMBER_NOT_EMPTY,SUBSET_DEF]))))
  >- (`!x. x IN M.dom ==> feval M (interpret M σ⦇n ↦ x⦈ ∘ v⦇n ↦ V n⦈) f = feval M (interpret M σ ∘ v)⦇n ↦ x⦈ f` suffices_by metis_tac[] >> rw[] >> irule feval_ffvs >> rw[] >> Cases_on `n' = n` >>
     rw[interpret_def,APPLY_UPDATE_THM] >> Cases_on `v n'` >> rw[interpret_def] (* 2 *)
     >- (Cases_on `n'' = n` >> fs[APPLY_UPDATE_THM,ffvs_def,tfvs_def] >> rw[] >>
        first_x_assum (qspec_then `n'` mp_tac) >> rw[tfvs_def])
     >- (AP_TERM_TAC >> irule LIST_EQ >> rw[EL_MAP] >> irule interpret_tfvs >> rw[] >> Cases_on `n''' = n` >> fs[APPLY_UPDATE_THM] >> first_x_assum (qspec_then `n'` mp_tac) >> fs[ffvs_def,tfvs_def] >>
        rw[] >> first_x_assum (qspec_then `tfvs (EL x' l)` mp_tac) >> rw[] >> fs[MEM_MAP] >>
	first_x_assum (qspec_then `EL x' l` mp_tac) >> rw[] >> metis_tac[EL_MEM]))
  >- (rw[EQ_IMP_THM]
     >- (qexists_tac `x` >> rw[] >>
        Q.MATCH_ASMSUB_ABBREV_TAC `interpret _ _ (| VV |-> _ |)` >>
        `feval M (interpret M σ⦇VV ↦ x⦈ ∘ v⦇n ↦ V VV⦈) f <=> feval M (interpret M σ ∘ v)⦇n ↦ x⦈ f` suffices_by
          metis_tac[] >>
        irule feval_ffvs >> rw[] >> Cases_on `n' = n` >> fs[APPLY_UPDATE_THM] >> fs[interpret_def,APPLY_UPDATE_THM] >>
        irule interpret_tfvs >> rw[] >> fs[ffvs_def,tfvs_def] >> `n <> y` by fs[] >> fs[] >> Cases_on `n'' = VV` >>
        fs[APPLY_UPDATE_THM,Abbr`VV`] >> rw[] >>
        `FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f)) /\ (ffvs (fsubst v⦇n ↦ V n⦈ f)) <> {} /\  VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) IN (ffvs (fsubst v⦇n ↦ V n⦈ f))` suffices_by metis_tac[VARIANT_NOTIN] >> rw[] (* 3 *)
          >- metis_tac[ffvs_FINITE]
          >- (fs[ffvs_fsubst] >> fs[MEMBER_NOT_EMPTY,IMAGE_DEF] >> rw[] (* 2 *)
            >- metis_tac[MEMBER_NOT_EMPTY]
	    >- (rw[Once EXTENSION] >> `∃x. (∃x'. x = tfvs (v⦇n ↦ V n⦈ x') ∧ x' ∈ ffvs f) /\ x <> ∅` suffices_by metis_tac[] >>
	        rw[PULL_EXISTS] >> qexists_tac `y` >> fs[APPLY_UPDATE_THM] >> metis_tac[MEMBER_NOT_EMPTY]))
          >- (`ffvs (fsubst v⦇n ↦ V n⦈ f) = BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` by metis_tac[ffvs_fsubst] >>
             `VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) ∈ BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` suffices_by metis_tac[] >>
	     simp[PULL_EXISTS] >> qexists_tac `n'` >> fs[APPLY_UPDATE_THM]))
     >- (qexists_tac `x` >> rw[] >>
        qabbrev_tac `VV = VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f))` >>
        `feval M (interpret M σ⦇VV ↦ x⦈ ∘ v⦇n ↦ V VV⦈) f <=> feval M (interpret M σ ∘ v)⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
	irule feval_ffvs >> rw[] >> Cases_on `n' = n` >> fs[APPLY_UPDATE_THM] >> fs[interpret_def,APPLY_UPDATE_THM] >>
        irule interpret_tfvs >> rw[] >> fs[ffvs_def,tfvs_def] >> `n <> y` by fs[] >> fs[] >> Cases_on `n'' = VV` >>
        fs[APPLY_UPDATE_THM,Abbr`VV`] >> rw[] >>
        `FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f)) /\ (ffvs (fsubst v⦇n ↦ V n⦈ f)) <> {} /\  VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) IN (ffvs (fsubst v⦇n ↦ V n⦈ f))` suffices_by metis_tac[VARIANT_NOTIN] >> rw[] (* 3 *)
          >- metis_tac[ffvs_FINITE]
          >- (fs[ffvs_fsubst] >> fs[MEMBER_NOT_EMPTY,IMAGE_DEF] >> rw[] (* 2 *)
            >- metis_tac[MEMBER_NOT_EMPTY]
	    >- (rw[Once EXTENSION] >> `∃x. (∃x'. x = tfvs (v⦇n ↦ V n⦈ x') ∧ x' ∈ ffvs f) /\ x <> ∅` suffices_by metis_tac[] >>
	        rw[PULL_EXISTS] >> qexists_tac `y` >> fs[APPLY_UPDATE_THM] >> metis_tac[MEMBER_NOT_EMPTY]))
          >- (`ffvs (fsubst v⦇n ↦ V n⦈ f) = BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` by metis_tac[ffvs_fsubst] >>
             `VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)) ∈ BIGUNION (IMAGE (tfvs ∘ v⦇n ↦ V n⦈) (ffvs f))` suffices_by metis_tac[] >>
	     simp[PULL_EXISTS] >> qexists_tac `n'` >> fs[APPLY_UPDATE_THM])))
  >- (`!x. x IN M.dom ==> feval M (interpret M σ⦇n ↦ x⦈ ∘ v⦇n ↦ V n⦈) f = feval M (interpret M σ ∘ v)⦇n ↦ x⦈ f` suffices_by metis_tac[] >> rw[] >> irule feval_ffvs >> rw[] >> Cases_on `n' = n` >>
     rw[interpret_def,APPLY_UPDATE_THM] >> Cases_on `v n'` >> rw[interpret_def] (* 2 *)
     >- (Cases_on `n'' = n` >> fs[APPLY_UPDATE_THM,ffvs_def,tfvs_def] >> rw[] >>
        first_x_assum (qspec_then `n'` mp_tac) >> rw[tfvs_def])
     >- (AP_TERM_TAC >> irule LIST_EQ >> rw[EL_MAP] >> irule interpret_tfvs >> rw[] >> Cases_on `n''' = n` >> fs[APPLY_UPDATE_THM] >> first_x_assum (qspec_then `n'` mp_tac) >> fs[ffvs_def,tfvs_def] >>
        rw[] >> first_x_assum (qspec_then `tfvs (EL x' l)` mp_tac) >> rw[] >> fs[MEM_MAP] >>
	first_x_assum (qspec_then `EL x' l` mp_tac) >> rw[] >> metis_tac[EL_MEM]))
QED
  


Theorem tsubst_V :
  !t. tsubst V t = t
Proof
  completeInduct_on `fterm_size t` >> rw[tsubst_def] >>
  Cases_on `t` >> rw[tsubst_def] >> irule LIST_EQ >> rw[EL_MAP] >>
  `fterm_size (EL x l) < fterm_size (Fn n l)` suffices_by metis_tac[] >> simp[fterm_size_def] >>
  `MEM (EL x l) l` by metis_tac[MEM_EL] >> drule tsize_lemma >> rw[]
QED

Theorem size_nonzero :
  !f. 0 < size f
Proof
  Induct_on `f` >> fs[size_def]
QED



Theorem fsubst_V :
  !f. fsubst V f = f
Proof
  completeInduct_on `size f` >> rw[] >> Cases_on `f` >> rw[fsubst_def] >> rw[tsubst_V] (* 8 *)
  >- (first_x_assum irule >> qexists_tac `size f'` >> rw[size_def] >> simp[size_nonzero])
  >- (first_x_assum irule >> qexists_tac `size f0` >> rw[size_def,size_nonzero])
  >- (Cases_on `y = n` >> fs[APPLY_UPDATE_THM] (* 2 *) >> fs[ffvs_def,tfvs_def])
  >- (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[ffvs_def,tfvs_def])
  >- (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[] >>
     first_x_assum irule >> qexists_tac `size f'` >> rw[size_def,size_nonzero])
  >- (Cases_on `y = n` >> fs[APPLY_UPDATE_THM] (* 2 *) >> fs[ffvs_def,tfvs_def])
  >> (`V⦇n ↦ V n⦈ = V` by (rw[FUN_EQ_THM] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM]) >> fs[ffvs_def,tfvs_def] >>
     first_x_assum irule >> qexists_tac `size f'` >> rw[size_def,size_nonzero])
QED


Theorem UPDATE_IMAGE :
  !σ n x s. IMAGE σ 𝕌(:num) ⊆ s /\ x IN s ==> IMAGE σ⦇n ↦ x⦈ 𝕌(:num) ⊆ s
Proof
  rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> fs[APPLY_UPDATE_THM] >> metis_tac[]
QED






Theorem Prenex_right_feval :
  !M σ f1 f2. M.dom <> {} ==> (feval M σ (Prenex_right f1 f2) <=> feval M σ (fIMP f1 f2))
Proof
  completeInduct_on `size f2` >> rw[Prenex_right_def,feval_def] >>
  Cases_on `f2` (* 6 *)
  >> fs[feval_def,Prenex_right_def] (* 2 *)
  >- (rw[EQ_IMP_THM]
     >- (`size f < size (fFORALL n f)` by rw[size_def] >>
        first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
        qabbrev_tac `VV = VARIANT (ffvs (fFORALL n f) ∪ ffvs f1)` >>
        `size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
        first_x_assum drule >> rw[] >>
        first_x_assum (qspecl_then [`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >>
        first_x_assum drule >> rw[] >>
        `feval M σ f1 = feval M σ⦇VV ↦ x⦈ f1` by
          (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
          `n' IN (ffvs (fFORALL n f) ∪ ffvs f1) /\ (ffvs (fFORALL n f) ∪ ffvs f1) <> {} /\
          FINITE (ffvs (fFORALL n f) ∪ ffvs f1)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
          rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
        rfs[] >> fs[feval_fsubst] >>
	`feval M σ⦇n ↦ x⦈ f = feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f` suffices_by metis_tac[] >>
        irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def] >> rw[] >>
        `VV IN (ffvs (fFORALL n f) ∪ ffvs f1) /\ FINITE (ffvs (fFORALL n f) ∪ ffvs f1) /\
	(ffvs (fFORALL n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
        rw[ffvs_FINITE,ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
     >- (Cases_on `feval M σ f1` (* 2 *)
       >- (`size f < size (fFORALL n f)` by fs[size_def] >> rpt (first_x_assum drule >> rw[]) >> 
	  qabbrev_tac `VV = VARIANT (ffvs (fFORALL n f) ∪ ffvs f1)` >>
 	  `size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
	  first_x_assum drule >> rw[] >>
	  first_x_assum (qspecl_then [`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >>
	  first_x_assum drule >> rw[] >> rw[feval_fsubst] >>
	  `feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f = feval M σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
	  irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[interpret_def,APPLY_UPDATE_THM] >> rw[] >>
	  `VV IN (ffvs (fFORALL n f) ∪ ffvs f1) /\ FINITE (ffvs (fFORALL n f) ∪ ffvs f1) /\
	  (ffvs (fFORALL n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	  rw[ffvs_FINITE,ffvs_def] >>
	  `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
       >- (qabbrev_tac `VV = VARIANT (ffvs (fFORALL n f) ∪ ffvs f1)` >>
          `size f < size (fFORALL n f)` by fs[size_def] >>
	  `size (fsubst V⦇n ↦ V VV⦈ f) = size f ` by metis_tac[size_fsubst] >>
	  rpt (first_x_assum drule >> rw[]) >>
	  first_x_assum (qspecl_then [`fsubst V⦇n ↦ V VV⦈ f`,`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >> rfs[] >>
	  `feval M σ f1 = feval M σ⦇VV ↦ x⦈ f1` suffices_by metis_tac[] >> irule feval_ffvs >> rw[] >>
	  Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >> 
          `VV IN (ffvs (fFORALL n f) ∪ ffvs f1) /\ FINITE (ffvs (fFORALL n f) ∪ ffvs f1) /\
 	  (ffvs (fFORALL n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
 	  rw[ffvs_FINITE,ffvs_def] >> metis_tac[MEMBER_NOT_EMPTY])))
>- (rw[EQ_IMP_THM] 
  >- (qexists_tac `x` >> rw[] >>
     `size f < size (fEXISTS n f)` by fs[size_def] >> first_x_assum drule >>
     rw[] >>
     qabbrev_tac `VV = VARIANT (ffvs (fEXISTS n f) ∪ ffvs f1)` >>
     `size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
     first_x_assum drule >> rw[] >>
     first_x_assum (qspecl_then [`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >>
     first_x_assum drule >> rw[] >>
     `feval M σ f1 = feval M σ⦇VV ↦ x⦈ f1` by
       (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
       `n' IN (ffvs (fEXISTS n f) ∪ ffvs f1) /\ (ffvs (fEXISTS n f) ∪ ffvs f1) <> {} /\
       FINITE (ffvs (fEXISTS n f) ∪ ffvs f1)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
       rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
     rfs[] >> fs[feval_fsubst] >>
     `feval M σ⦇n ↦ x⦈ f = feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f` suffices_by metis_tac[] >>
     irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def] >> rw[] >>
     `VV IN (ffvs (fEXISTS n f) ∪ ffvs f1) /\ FINITE (ffvs (fEXISTS n f) ∪ ffvs f1) /\
	(ffvs (fEXISTS n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
     rw[ffvs_FINITE,ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
  >- (Cases_on `feval M σ f1` (* 2 *)
     >- (first_x_assum drule >> rw[] >> qexists_tac `x` >> rw[] >>
        `size f < size (fEXISTS n f)` by fs[size_def] >> first_x_assum drule >>
	rw[] >>
	qabbrev_tac `VV = VARIANT (ffvs (fEXISTS n f) ∪ ffvs f1)` >>
	`size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
	first_x_assum drule >> rw[] >>
	first_x_assum (qspecl_then [`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >>
	first_x_assum drule >> rw[] >> rw[feval_fsubst] >>
	`feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f = feval M σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
	irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[interpret_def,APPLY_UPDATE_THM] >> rw[] >>
	`VV IN (ffvs (fEXISTS n f) ∪ ffvs f1) /\ FINITE (ffvs (fEXISTS n f) ∪ ffvs f1) /\
	(ffvs (fEXISTS n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	rw[] (* 3 *)
	>- fs[ffvs_def] >- metis_tac[ffvs_FINITE] >- metis_tac[ffvs_FINITE]
	>> fs[ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
     >- (fs[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `x` >> rw[] >>
        `size f < size (fEXISTS n f)` by fs[size_def] >> first_x_assum drule >>
	rw[] >>
	qabbrev_tac `VV = VARIANT (ffvs (fEXISTS n f) ∪ ffvs f1)` >>
	`size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
	first_x_assum drule >> rw[] >>
	first_x_assum (qspecl_then [`M`,`σ⦇VV ↦ x⦈`,`f1`] assume_tac) >>
	`(feval M σ⦇VV ↦ x⦈ (Prenex_right f1 (fsubst V⦇n ↦ V VV⦈ f)) ⇔
        feval M σ⦇VV ↦ x⦈ f1 ⇒ feval M σ⦇VV ↦ x⦈ (fsubst V⦇n ↦ V VV⦈ f))` by metis_tac[] >>
	rw[] >> `feval M σ⦇VV ↦ x⦈ f1 = feval M σ f1` suffices_by metis_tac[] >>
	irule feval_ffvs >> rw[] >> Cases_on `n' = VV` >> fs[APPLY_UPDATE_THM] >>
	`VV IN (ffvs (fEXISTS n f) ∪ ffvs f1) /\ FINITE (ffvs (fEXISTS n f) ∪ ffvs f1) /\
	(ffvs (fEXISTS n f) ∪ ffvs f1) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	rw[] (* 3 *)
	>- metis_tac[ffvs_FINITE] >- metis_tac[ffvs_FINITE]
	>- metis_tac[MEMBER_NOT_EMPTY])))
QED

Theorem Prenex_left_feval :
  !f1 f2 M σ. M.dom <> {} ==> (feval M σ (Prenex_left f1 f2) <=> (feval M σ (fIMP f1 f2)))
Proof
  completeInduct_on `size f1` >> rw[Prenex_left_def,feval_def,Prenex_right_feval] >>
  Cases_on `f1` (* 6 *)
  >> fs[feval_def,Prenex_left_def,Prenex_right_feval] >> rw[] (* 2 *)
  >- (rw[EQ_IMP_THM]
     >- (qabbrev_tac `VV = VARIANT (ffvs (fFORALL n f) ∪ ffvs f2)` >>
        `size f < size (fFORALL n f)` by rw[size_def] >> rpt (first_x_assum drule >> rw[]) >>
        `size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >> rpt (first_x_assum drule >> rw[]) >>
        first_x_assum (qspecl_then [`f2`,`σ⦇VV ↦ x⦈`] assume_tac) >> rfs[] >> 
        `feval M σ f2 = feval M σ⦇VV ↦ x⦈ f2` by
          (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
          `n' IN (ffvs (fFORALL n f) ∪ ffvs f2) /\ (ffvs (fFORALL n f) ∪ ffvs f2) <> {} /\
          FINITE (ffvs (fFORALL n f) ∪ ffvs f2)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
          rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
        rfs[] >> fs[feval_fsubst] >>
	`feval M σ⦇n ↦ x⦈ f = feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f` suffices_by metis_tac[] >>
        irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def] >> rw[] >>
        `VV IN (ffvs (fFORALL n f) ∪ ffvs f2) /\ FINITE (ffvs (fFORALL n f) ∪ ffvs f2) /\
	(ffvs (fFORALL n f) ∪ ffvs f2) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
        rw[ffvs_FINITE,ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
     >- (qabbrev_tac `VV = VARIANT (ffvs (fFORALL n f) ∪ ffvs f2)` >> 
        `size f < size (fFORALL n f)` by fs[size_def] >> rpt (first_x_assum drule >> rw[]) >>
	`size f = size (fsubst V⦇n ↦ V VV⦈ f)` by metis_tac[size_fsubst] >>
        rpt (first_x_assum drule >> rw[]) >>
	Cases_on `(∀x. x ∈ M.dom ⇒ feval M σ⦇n ↦ x⦈ f)`
	>- (fs[GSYM MEMBER_NOT_EMPTY] >> first_x_assum drule >> rw[] >>
	   first_x_assum (qspecl_then [`f2`,`σ⦇VV ↦ x⦈`] assume_tac) >>
	   `feval M σ f2 = feval M σ⦇VV ↦ x⦈ f2` by
           (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
           `n' IN (ffvs (fFORALL n f) ∪ ffvs f2) /\ (ffvs (fFORALL n f) ∪ ffvs f2) <> {} /\
           FINITE (ffvs (fFORALL n f) ∪ ffvs f2)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
           rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
	   rfs[] >> `feval M σ⦇VV ↦ x⦈ (Prenex_left (fsubst V⦇n ↦ V VV⦈ f) f2)` by metis_tac[] >> metis_tac[])
	>- (fs[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `x'` >> fs[feval_fsubst] >> rw[] >>
	   `feval M σ⦇n ↦ x'⦈ f = feval M (interpret M σ⦇VV ↦ x'⦈ ∘ V⦇n ↦ V VV⦈) f` suffices_by metis_tac[] >>
	   irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def] >> rw[] >>
	   `VV IN (ffvs (fFORALL n f) ∪ ffvs f2) /\ FINITE (ffvs (fFORALL n f) ∪ ffvs f2) /\
	   (ffvs (fFORALL n f) ∪ ffvs f2) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	   rw[ffvs_FINITE,ffvs_def] >> 
           `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])))
  >- (qabbrev_tac `VV = VARIANT (ffvs (fEXISTS n f) ∪ ffvs f2)` >> 
     `size f < size (fEXISTS n f)` by fs[size_def] >>
     `size (fsubst V⦇n ↦ V VV⦈ f) = size f` by metis_tac[size_fsubst] >> rpt (first_x_assum drule >> rw[]) >>
     first_x_assum (qspecl_then [`(fsubst V⦇n ↦ V VV⦈ f)`,`f2`,`M`] assume_tac) >> rw[EQ_IMP_THM] (* 2 *)
     >- (fs[feval_fsubst] >> first_x_assum drule >> rw[] >> 
        `feval M σ f2 = feval M σ⦇VV ↦ x⦈ f2` by
          (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
          `n' IN (ffvs (fEXISTS n f) ∪ ffvs f2) /\ (ffvs (fEXISTS n f) ∪ ffvs f2) <> {} /\
          FINITE (ffvs (fEXISTS n f) ∪ ffvs f2)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
          rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
        `feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f = feval M σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
	irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[interpret_def,APPLY_UPDATE_THM] >> rw[] >>
        `VV IN (ffvs (fEXISTS n f) ∪ ffvs f2) /\ FINITE (ffvs (fEXISTS n f) ∪ ffvs f2) /\
	(ffvs (fEXISTS n f) ∪ ffvs f2) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	rw[ffvs_FINITE,ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
     >- (fs[feval_fsubst,GSYM MEMBER_NOT_EMPTY] >>
        `feval M σ f2 = feval M σ⦇VV ↦ x⦈ f2` by
          (irule feval_ffvs >> rw[] >> Cases_on `VV = n'` >> fs[APPLY_UPDATE_THM] >>
          `n' IN (ffvs (fEXISTS n f) ∪ ffvs f2) /\ (ffvs (fEXISTS n f) ∪ ffvs f2) <> {} /\
          FINITE (ffvs (fEXISTS n f) ∪ ffvs f2)` suffices_by metis_tac[VARIANT_NOTIN,Abbr`n'`] >>
          rw[ffvs_FINITE,ffvs_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
	`∃x. x ∈ M.dom ∧ feval M σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >> qexists_tac `x` >> rw[] >>
        `feval M (interpret M σ⦇VV ↦ x⦈ ∘ V⦇n ↦ V VV⦈) f = feval M σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
	irule feval_ffvs >> rw[] >> Cases_on `n = n'` >> fs[interpret_def,APPLY_UPDATE_THM] >> rw[] >>
        `VV IN (ffvs (fEXISTS n f) ∪ ffvs f2) /\ FINITE (ffvs (fEXISTS n f) ∪ ffvs f2) /\
	(ffvs (fEXISTS n f) ∪ ffvs f2) <> {}` suffices_by metis_tac[VARIANT_NOTIN,Abbr`VV`] >>
	rw[ffvs_FINITE,ffvs_def] >> `ffvs f DELETE n ≠ ∅` suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[]))   
QED


Theorem Prenex_feval:
  !M σ f. M.dom <> {} ==> (feval M σ f <=> feval M σ (Prenex f))
Proof
  completeInduct_on `size f` >> Cases_on `f` >> fs[feval_def,Prenex_def,Prenex_right_feval,Prenex_left_feval] >> rw[] (* 3 *)
  >- (`size f' < size (fIMP f' f0) /\ size f0 < size (fIMP f' f0)` by rw[size_def,size_nonzero] >>
     first_assum (qspec_then `size f'` mp_tac) >> rw[])
  >- (`size f' < size (fFORALL n f')` by fs[size_def] >> first_x_assum drule >> rw[])
  >- (`size f' < size (fEXISTS n f')` by fs[size_def] >> first_x_assum drule >> rw[])
QED

Theorem SKOLEM_qfree :
  !f. qfree f ==> SKOLEM n f = f
Proof
  Induct_on `f` >> fs[qfree_def,SKOLEM_def]
QED


Theorem tsubst_tsubst :
  !t v2 v1. tsubst v2 (tsubst v1 t) = tsubst (tsubst v2 ∘ v1) t
Proof
  completeInduct_on `fterm_size t` >> Cases_on `t` >> fs[tsubst_def] >>
  rw[MAP_MAP_o] >> qmatch_abbrev_tac `MAP f1 l = MAP f2 l` >>
  irule LIST_EQ >> rw[EL_MAP] >>
  `MEM (EL x l) l` by fs[EL_MEM] >>
  `!m. MEM m l ==> f1 m = f2 m` suffices_by metis_tac[] >> rw[] >>
  drule tsize_lemma >> rw[] >> 
  first_x_assum (qspec_then `fterm_size m` mp_tac) >> fs[] >> rw[] >>
  first_x_assum (qspec_then `m` mp_tac) >> fs[] >> rw[Abbr`f1`,Abbr`f2`]
QED


Theorem MAP_LIST_EQ :
  !l f g. (!m. MEM m l ==> f m = g m) ==> MAP f l = MAP g l
Proof
  rw[] >> irule LIST_EQ >> rw[EL_MAP] >> metis_tac[EL_MEM]
QED

Theorem tfvs_tsubst_EQ :
  !t v1 v2. (!a. a IN (tfvs t) ==> v1 a = v2 a) ==> tsubst v1 t = tsubst v2 t
Proof
  completeInduct_on `fterm_size t` >> rw[] >> Cases_on `t` >> 
  fs[tsubst_def,tfvs_def] >> irule MAP_LIST_EQ >> rw[] >> 
  drule tsize_lemma >> rw[] >> 
  last_x_assum (qspec_then `fterm_size m` mp_tac) >> rpt strip_tac >> rfs[] >>
  first_x_assum (qspec_then `m` mp_tac) >> rw[] >> fs[] >>
  first_x_assum irule >> rw[] >> first_x_assum irule >> qexists_tac `tfvs m` >> 
  rw[MEM_MAP] >> metis_tac[]
QED

Theorem ffvs_fsubst_EQ :
  !f v1 v2. (!a. a IN (ffvs f) ==> v1 a = v2 a) ==> fsubst v1 f = fsubst v2 f
Proof
  completeInduct_on `size f` >> rw[] >> Cases_on `f` >> 
  fs[fsubst_def,ffvs_def,tfvs_tsubst_EQ,size_def,size_nonzero] >> rw[] (* 14 *)
  >- (rpt AP_TERM_TAC >> first_x_assum irule >> rw[] >> Cases_on `n = a` >>
     fs[APPLY_UPDATE_THM])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (first_assum irule >> rw[] >> Cases_on `n = a` >> fs[APPLY_UPDATE_THM] >>
     `(fsubst v1⦇a ↦ V a⦈ f') = (fsubst v2⦇a ↦ V a⦈ f')` 
       suffices_by metis_tac[] >>
     rfs[] >> first_x_assum irule >> rw[] >> Cases_on `a = a'` >> 
     fs[APPLY_UPDATE_THM])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (first_x_assum irule >> rw[] >> Cases_on `n = a` >> fs[APPLY_UPDATE_THM])
  >- (rpt AP_TERM_TAC >> first_x_assum irule >> rw[] >> Cases_on `n = a` >>
     fs[APPLY_UPDATE_THM])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (first_assum irule >> rw[] >> Cases_on `n = a` >> fs[APPLY_UPDATE_THM] >>
     `(fsubst v1⦇a ↦ V a⦈ f') = (fsubst v2⦇a ↦ V a⦈ f')` 
       suffices_by metis_tac[] >>
     rfs[] >> first_x_assum irule >> rw[] >> Cases_on `a = a'` >> 
     fs[APPLY_UPDATE_THM])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (`tfvs (v1⦇n ↦ V n⦈ y) = tfvs (v2⦇n ↦ V n⦈ y)` suffices_by metis_tac[] >>
     Cases_on `n = y` >> fs[APPLY_UPDATE_THM,tfvs_def])
  >- (first_x_assum irule >> rw[] >> Cases_on `n = a` >> fs[APPLY_UPDATE_THM])
QED


Theorem SKOLEM_qfree :
  !f. qfree f ==> SKOLEM n f = f
Proof
  Induct_on `f` >> fs[qfree_def,SKOLEM_def]
QED

Theorem specialize_qfree :
  ! f. qfree f ==> specialize f = f
Proof
  Induct_on `f` >> fs[qfree_def,specialize_def]
QED



Theorem fsubst_fsubst :
  !f v1 v2. fsubst v2 (fsubst v1 f) = fsubst ((tsubst v2) o v1) f
Proof
  completeInduct_on `size f` >> rw[] >> Cases_on `f` >> rw[] (* 6 *)
  >- fs[fsubst_def]
  >- rw[fsubst_def,tsubst_tsubst] (* 2 *)
  >- rw[fsubst_def,tsubst_tsubst]
  >- (rw[fsubst_def] (* 2 *)
     >- (first_x_assum (qspec_then `size f'` mp_tac) >> rw[size_def,size_nonzero]) >>  first_x_assum (qspec_then `size f0` mp_tac) >> rw[size_def,size_nonzero])
  >- first_x_assum (qspec_then `size f'` mp_tac) >> rpt strip_tac >> fs[size_def] >>
     first_x_assum (qspec_then `f'` mp_tac) >> rpt strip_tac >> fs[] >>
     simp[Once fsubst_def,SimpLHS] >> rw[] (* 2 *)
     >- qabbrev_tac `a = (VARIANT (ffvs (fsubst v1⦇n ↦ V n⦈ f')))` >>
        rw[Once fsubst_def] (* 2 *)
        >- qabbrev_tac 
           `b = (VARIANT (ffvs (fsubst (tsubst v2⦇a ↦ V a⦈ ∘ v1⦇n ↦ V a⦈) f')))` >> 
           rw[Once fsubst_def,SimpRHS] (* 4 *) 
           >- Cases_on `a = y'` >> fs[APPLY_UPDATE_THM,ffvs_def] >> rfs[] >> 
              rw[Abbr`b`] >> rpt AP_TERM_TAC >> irule ffvs_fsubst_EQ >> rw[] >>
              Cases_on `n = a` >> fs[APPLY_UPDATE_THM,tsubst_def] (* 2 *)
              >- (rw[APPLY_UPDATE_THM,tsubst_def] >> irule tfvs_tsubst_EQ >>
                 rw[] >> `a <> a''` suffices_by fs[APPLY_UPDATE_THM] >> 
                 strip_tac >> fs[] >> 
                 `(ffvs (fsubst v1⦇a'' ↦ V a''⦈ f')) <> {} /\
                  FINITE (ffvs (fsubst v1⦇a'' ↦ V a''⦈ f')) /\
                  a'' IN (ffvs (fsubst v1⦇a'' ↦ V a''⦈ f'))`
                   suffices_by metis_tac[VARIANT_NOTIN] >>
                 rw[ffvs_FINITE] (* 2 *)
                 >- (rw[ffvs_fsubst] (* 2 *) >- (strip_tac >> fs[]) >>
                    rw[IMAGE_DEF] >>
                    `?x. x IN (ffvs f') /\ tfvs (v1⦇a ↦ V a⦈ x) <> {}`
                      suffices_by (rw[] >> rw[Once EXTENSION] >> 
                       qexists_tac `tfvs (v1⦇a ↦ V a⦈ x)` >> rw[] >>
                       metis_tac[]) >>
                    qexists_tac `y` >> fs[APPLY_UPDATE_THM] >> strip_tac >> fs[])
                 >- (rw[ffvs_fsubst,PULL_EXISTS] >> qexists_tac `a'` >> 
                    fs[APPLY_UPDATE_THM]))
              >- rw[APPLY_UPDATE_THM,tsubst_def] (* 2 *)
                 >- fs[ffvs_fsubst,tfvs_tsubst] >> Cases_on `a' = x` >>
                    fs[tfvs_def,APPLY_UPDATE_THM] >> 






                    `(BIGUNION (IMAGE (tfvs ∘ v1⦇a' ↦ V a'⦈) (ffvs f'))) <> {} /\
                     FINITE (BIGUNION (IMAGE (tfvs ∘ v1⦇a' ↦ V a'⦈) (ffvs f'))) /\
                     a IN (BIGUNION (IMAGE (tfvs ∘ v1⦇a' ↦ V a'⦈) (ffvs f')))`
                      suffices_by metis_tac[VARIANT_NOTIN] >> rw[] (* 4 *)
                    >- (strip_tac >> fs[])
                    >- (rw[IMAGE_DEF] >>
                       `?x. x IN (ffvs f') /\ tfvs (v1⦇a' ↦ V a'⦈ x) <> {}`
                        suffices_by (rw[] >> rw[Once EXTENSION] >> 
                        qexists_tac `tfvs (v1⦇a' ↦ V a'⦈ x'')` >> rw[] >>
                        metis_tac[]) >>
                       qexists_tac `y` >> fs[APPLY_UPDATE_THM] >> strip_tac >> fs[])
                    >- metis_tac[tfvs_FINITE]
                    >- rw[PULL_EXISTS] >> qexists_tac `y` >> fs[APPLY_UPDATE_THM]
 
              
        
     










     >- qabbrev_tac `a = (VARIANT (ffvs (fsubst v1⦇n ↦ V n⦈ f')))` >>
        rw[Once fsubst_def] (* 2 *)
        >- qabbrev_tac `b = (VARIANT (ffvs (fsubst (tsubst v2⦇a ↦ V a⦈ ∘ v1⦇n ↦ V a⦈) f')))` >> rw[Once fsubst_def] (* 4 *)
           >- 
           >- qabbrev_tac 
              `c = (VARIANT (ffvs (fsubst (tsubst v2 ∘ v1)⦇n ↦ V n⦈ f')))` >>    
              irule ffvs_fsubst_EQ >> rw[] >> 
              Cases_on `n = a'` >> fs[APPLY_UPDATE_THM] (* 2 *)
              >- rw[tsubst_def,APPLY_UPDATE_THM,Abbr`b`,Abbr`c`] >> rpt AP_TERM_TAC >>
                 irule ffvs_fsubst_EQ >> rw[] >>
                 Cases_on `a' = a''` >> fs[APPLY_UPDATE_THM] (* 2 *)
                 >- rw[tsubst_def,APPLY_UPDATE_THM] >> 
                    Cases_on `a' = y` >> Cases_on `a' = y''` >> Cases_on `a = y'` >>
                    fs[ffvs_def] >> 
                    `FINITE (ffvs (fsubst v1⦇a' ↦ V a'⦈ f')) /\ 
                     (ffvs (fsubst v1⦇a' ↦ V a'⦈ f')) <> {} /\
                     a IN (ffvs (fsubst v1⦇a' ↦ V a'⦈ f'))`
                       suffices_by metis_tac[VARIANT_NOTIN] >> rw[ffvs_FINITE] (* 2 *)
                    >- (fs[ffvs_fsubst] >> rw[]
                       >- (strip_tac >> fs[])
                       >- (simp[Once EXTENSION,IMAGE_DEF,EQ_IMP_THM,PULL_EXISTS] >> 
                          rw[PULL_EXISTS] >>
                          `∃x. (∃x'. (x = tfvs (v1⦇a' ↦ V a'⦈ x') ∧ x' ∈ ffvs f') ∧
                            tfvs (v1⦇a' ↦ V a'⦈ x') ≠ ∅)` suffices_by metis_tac[] >>
                          rw[PULL_EXISTS] >> 
                          qexists_tac `a'` >> fs[APPLY_UPDATE_THM,tfvs_def]))
                    >- fs[ffvs_fsubst,tfvs_tsubst,PULL_EXISTS] >> 
                       Cases_on `a' = x` >> fs[APPLY_UPDATE_THM,tfvs_def] >> 


           qpat_x_assum `!x. _` (assume_tac o GSYM) >>
           fs[] >> rw[fsubst_def]




    
           simp[Once fsubst_def] >> rw[] (* 4 *)
           >- 
           >-
           >- qabbrev_tac `c = (VARIANT (ffvs (fsubst (tsubst v2 ∘ v1)⦇n ↦ V n⦈ f')))` >>
               qpat_x_assum `!v1 v2. _` (assume_tac o GSYM) >> fs[] >>
               

`(tsubst v2⦇a ↦ V b⦈ ∘ v1⦇n ↦ V a⦈) = (tsubst v2 ∘ v1)⦇n ↦ V c⦈` suffices_by metis_tac[] >>
simp[FUN_EQ_THM] >> rw[] >> Cases_on `x = n` >> fs[APPLY_UPDATE_THM] (*2 *)
>- rw[tsubst_def,APPLY_UPDATE_THM,Abbr`b`,Abbr`c`] >> rpt AP_TERM_TAC >>
   `(tsubst v2⦇a ↦ V a⦈ ∘ v1⦇n ↦ V a⦈) = (tsubst v2 ∘ v1)⦇n ↦ V n⦈`
   suffices_by metis_tac[] >> rw[FUN_EQ_THM] >> Cases_on `n = x` >> fs[APPLY_UPDATE_THM] (* 2 *)
   >- rw[tsubst_def,APPLY_UPDATE_THM] >> cheat
      Cases_on `v1 x` >> fs[tsubst_def] >> cheat >> 
      irule LIST_EQ >> rw[] >> rw[EL_MAP] >> 
      `!m. MEM m l ==> tsubst v2⦇a ↦ V a⦈ m = tsubst v2 m` suffices_by 
        metis_tac[MEM_EL] >>
      rw[] >> 
   
           
     
     

     
QED



Theorem prenex_SKOLEM_fsubst :
  !f. prenex f ==>
    (!n v. (SKOLEM n (fsubst v f)) = (fsubst v (SKOLEM n f)))
Proof
completeInduct_on `size f` >> 
`∀f.
       prenex f ⇒ v = size f ⇒
       ∀n v. SKOLEM n (fsubst v f) = fsubst v (SKOLEM n f)` suffices_by metis_tac[] >> Induct_on `prenex f` >> rw[]
>- rw[SKOLEM_qfree]
>- first_x_assum (qspec_then `size f` mp_tac) >> rw[size_def] >>
   rw[fsubst_def,SimpLHS] (* 2 *)
   >- qabbrev_tac `a = (VARIANT (ffvs (fsubst v'⦇n ↦ V n⦈ f)))` >>
      rw[SKOLEM_def,SimpLHS] >>
      qmatch_abbrev_tac `SKOLEM (n' + 1) (fsubst V⦇a ↦ b⦈ _ ) = _` >>
      `size (fsubst v'⦇n ↦ V a⦈ f) = size f` by metis_tac[size_fsubst] >>
      first_x_assum (qspec_then `(fsubst v'⦇n ↦ V a⦈ f)` mp_tac) >> rw[] >>
      rw[SKOLEM_def] >> 
      qmatch_abbrev_tac `_ = fsubst v' (SKOLEM (n' + 1) fsubst V⦇n ↦ c⦈ f))` >>
      `SKOLEM (n' + 1) (fsubst V⦇a ↦ b⦈ (fsubst v'⦇n ↦ V a⦈ f))= SKOLEM (n' + 1) (fsubst v' (fsubst V⦇n ↦ c⦈ f))` suffices_by cheat >> AP_TERM_TAC >>
      `!f v1 v2. fsubst v2 (fsubst v1 f) = fsubst ((tsubst v2) o v1) f`
      by cheat >> rw[] >> irule ffvs_fsubst_EQ >> rw[] >> 
      Cases_on `n = a'` >> fs[APPLY_UPDATE_THM] (* 2 *)
      >- rfs[ffvs_def]
     

QED

Theorem prenex_SKOLEM_fsubst :
  !f. prenex f ==>
    (!n v M σ. feval M σ (SKOLEM n (fsubst v f)) = feval M σ (fsubst v (SKOLEM n f)))
Proof
completeInduct_on `size f` >> 
`∀f.
       prenex f ⇒  v = size f ==>
       ∀n v M σ.
           feval M σ (SKOLEM n (fsubst v f)) ⇔
           feval M σ (fsubst v (SKOLEM n f))` suffices_by metis_tac[] >>
Induct_on `prenex f` >> rw[]
>- rw[SKOLEM_qfree]
>- first_x_assum (qspec_then `size f` mp_tac) >> rw[size_def] >>
   first_x_assum (qspec_then `f` mp_tac) >> rw[fsubst_def] >> 
   qabbrev_tac `a = (VARIANT (ffvs (fsubst v'⦇n ↦ V n⦈ f)))` >>
   rw[SKOLEM_def] >>  
   qabbrev_tac `b = Fn ((a ⊗ num_of_form (fsubst v'⦇n ↦ V a⦈ f)) ⊗ n')
                (MAP V
                   (SET_TO_LIST (ffvs (fEXISTS a (fsubst v'⦇n ↦ V a⦈ f)))))` >>
   qabbrev_tac `c = Fn ((n ⊗ num_of_form f) ⊗ n')
                   (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
   
   



  >- qabbrev_tac `a = (VARIANT (ffvs (fsubst v⦇n ↦ V n⦈ f)))` >>
     rw[SKOLEM_def] >> rw[ffvs_def,ffvs_fsubst] >>
     qmatch_abbrev_tac `SKOLEM (n' + 1) (fsubst V(|a |-> fn |) fv) = _` >>
     qmatch_abbrev_tac `_ = fsubst v (fsubst V(| n |-> fn' |) (SKOLEM (n' + 1) f))` >>
     rw[Abbr`fv`] >> 
     `!v1 v2 f. fsubst v2 (fsubst v1 f) = fsubst ((tsubst v2) o v1) f` by cheat >> fs[] >>
     irule ffvs_fsubst_EQ >> rw[] >> 
     `a <> n` by strip_tac >> fs[] >>  
       `(ffvs (fsubst v⦇n ↦ V n⦈ f)) <> {} /\ FINITE (ffvs (fsubst v⦇n ↦ V n⦈ f)) /\
        n IN (ffvs (fsubst v⦇n ↦ V n⦈ f))` suffices_by metis_tac[VARIANT_NOTIN] >>
        rw[ffvs_FINITE] (* 2 *)
        >- rw[ffvs_fsubst] (* 2 *) >- (strip_tac >> fs[]) >> cheat
     fs[APPLY_UPDATE_THM,ffvs_fsubst,PULL_EXISTS] >> qexists_tac `y` >> fs[]

QED


``fsubst v2 (fsubst v1 f) = fsubst ((tsubst v2) o v1) f``



Theorem SKOLEM_qfree :
  !f. qfree f ==> SKOLEM n f = f
Proof
  Induct_on `f` >> fs[qfree_def,SKOLEM_def]
QED
Theorem SKOLEM_feval :
  !f n. prenex f ==> 
        ((?M:α folmodel σ. feval M σ  (SKOLEM n f)) <=> 
        (?M:α folmodel σ. feval M σ f))
Proof
  completeInduct_on `size f` >> fs[PULL_FORALL] >> Cases_on `f` >> 
  simp[SKOLEM_def,size_def,feval_def] >> rw[] (* 3 *)
  >- 
QED


Theorem SKOLEM_qfree :
  !f. qfree f ==> SKOLEM n f = f
Proof
  Induct_on `f` >> fs[qfree_def,SKOLEM_def]
QED

Theorem specialize_qfree :
  ! f. qfree f ==> specialize f = f
Proof
  Induct_on `f` >> fs[qfree_def,specialize_def]
QED





(* val _ = Datatype`
        folmodel = <| dom : 'a set ;
                      fnsyms : num -> 'a list -> 'a;
                      predsyms : num -> 'a -> bool;
                      relsyms : num -> 'a -> 'a -> bool;
                      |>`; 
*)

          

Theorem SKOLEM_fsubst :
  !f. prenex f ==> 
    !M σ n v. feval M σ (SKOLEM n (fsubst v f)) <=> feval M σ (fsubst v (SKOLEM n f))  
Proof
  Induct_on `prenex f` >> rw[SKOLEM_qfree,SKOLEM_def] 
  >- qabbrev_tac `a = Fn ((n ⊗ num_of_form f) ⊗ n')
                   (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
     `feval M σ (SKOLEM n' (fsubst v (fEXISTS n f))) = 
     feval M σ (fsubst v (SKOLEM n' (fEXISTS n f)))` by cheat >> rw[] >>
     rw[SKOLEM_def]
  >- `feval M σ (SKOLEM n' (fsubst v (fFORALL n f))) = 
     feval M σ (fsubst v (SKOLEM n' (fFORALL n f)))` by cheat >> rw[SKOLEM_def]
QED



Theorem prenex_SKOLEM_implies_original :
  !f. prenex f ==> (!M σ n. (!k l. (M.fnsyms k l) IN M.dom) ==> (feval M σ (SKOLEM n f) ==> feval M σ f))
Proof
completeInduct_on `size f` >> 
`∀f. prenex f ⇒  v = size f ⇒ ∀M σ n. (∀k l. M.fnsyms k l ∈ M.dom) ==> 
         feval M σ (SKOLEM n f) ⇒ feval M σ f`
  suffices_by metis_tac[] >> Induct_on `prenex f` >> rw[]
>- metis_tac[SKOLEM_qfree]    
>- (fs[SKOLEM_qfree,SKOLEM_def,feval_def] >>
   qabbrev_tac `a = Fn ((n ⊗ num_of_form f) ⊗ n')
                      (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
   qexists_tac `interpret M σ a` >> rw[] (* 2 *)
   >- rw[Abbr`a`,interpret_def]
   >- (`feval M σ (fsubst V⦇n ↦ a⦈ f)` by 
      (last_x_assum (qspec_then `size f` mp_tac) >> rw[size_def] >>
       first_x_assum (qspec_then `fsubst V⦇n ↦ a⦈ f` mp_tac) >> 
      rw[size_fsubst,GSYM prenex_fsubst] >> metis_tac[]) >>
      fs[feval_fsubst] >>
      `feval M σ⦇n ↦ interpret M σ a⦈ f = feval M (interpret M σ ∘ V⦇n ↦ a⦈) f`
        suffices_by metis_tac[] >>
      irule feval_ffvs >> rw[] >>
      Cases_on `n = n''` >> fs[APPLY_UPDATE_THM] >> rw[interpret_def]))
>- (fs[SKOLEM_qfree,SKOLEM_def,feval_def] >> rw[] >>
   first_assum drule >> strip_tac >> 
   last_x_assum (qspec_then `size f` mp_tac) >> rw[size_def] >>
   first_x_assum (qspec_then `f` mp_tac) >> rw[] >> metis_tac[])
QED 

Theorem SKOLEM_fsubst :
  !f n. prenex f ==> SKOLEM n (fsubst v f) = fsubst v⦇n ↦ V z⦈ (SKOLEM n f)
Proof

QED


Theorem SKOLEM_n_feval :
  !f. prenex f ==> !M σ. feval M σ f ==> !n. ?M σ. feval M σ (SKOLEM n f)
Proof

QED
 

Theorem SKOLEM_fsatis :
  !f. prenex f ==> (!M:α folmodel σ n. (!k l. (M.fnsyms k l) IN M.dom)) ==>
        ((?M:α folmodel σ. fsatis M σ (SKOLEM n f)) <=> 
        (?M:α folmodel σ. fsatis M σ f))
Proof
Induct_on `prenex` >> rw[SKOLEM_qfree,EQ_IMP_THM,specialize_qfree] (* 4 *)
>- (map_every qexists_tac [`M`,`σ`] >>
   metis_tac[prenex_SKOLEM_implies_original,prenex_rules,fsatis_def])
>- first_x_assum drule >> rw[] >> fs[fsatis_def,feval_def,PULL_EXISTS] >> 
   rw[SKOLEM_def] >> 
   qmatch_abbrev_tac `∃M' σ'. IMAGE σ' 𝕌(:num) ⊆ M'.dom ∧
       feval M' σ' (SKOLEM (n + 1) (fsubst V⦇n' ↦ a⦈ f))` >>
   `IMAGE σ⦇n' ↦ x⦈ 𝕌(:num) ⊆ M.dom` by metis_tac[UPDATE_IMAGE] >>
   first_x_assum drule >> rw[] >> 
   
  
 




  >- rfs[ffvs_def,APPLY_UPDATE_THM] >> 


     `∃M σ. fsatis M σ (fNOT (fEXISTS n (fNOT f)))` suffices_by cheat >>
     fs[fsatis_def,feval_def,fNOT_def] >> 
     fs[SKOLEM_def] >> 
     `!a. a IN M.dom ==> fsatis M σ (SKOLEM n' f)` by cheat >> 
     
  fs[PULL_EXISTS] >> SPOSE_NOT_THEN ASSUME_TAC
     `fsatis 


 
  >- fs[SKOLEM_def] >>

     qabbrev_tac `a = Fn ((n ⊗ num_of_form f) ⊗ n')
                      (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
     rw[feval_def] >> 
     `feval M σ (fsubst V⦇n ↦ a⦈ (specialize (SKOLEM (n' + 1) f)))` by cheat (*need SKOLEM fsubst commutes*)>>
     fs[feval_fsubst] >> 
     `?M σ. feval M σ f` by metis_tac[] >> map_every qexists_tac [`M'`,`σ'`,`σ' n`] >> cheat

  >- rw[SKOLEM_def] >>
     qabbrev_tac `a = Fn ((n ⊗ num_of_form f) ⊗ n')
                    (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
     fs[feval_def] >> 
     `∃M' σ'. feval M' σ' (fsubst V⦇n ↦ a⦈ (specialize (SKOLEM (n' + 1) f)))` suffices_by cheat (* require comm *) >>
     `?M σ. feval M σ (specialize (SKOLEM (n' + 1) f))` by metis_tac[] >>
     (* same σ', add M' a new function symbol Fn ((n ⊗ num_of_form f) ⊗ n')
              (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))) and interpret it as σ'. *)
   cheat
     rw[feval_fsubst]
  >- fs[SKOLEM_def,feval_def,specialize_def] >> 
     `x IN M.dom` by cheat >>
     first_x_assum drule >> rw[] >> `?M σ. feval M σ f` by metis_tac[] >>
     (*strengthen the inductive hypothesis?*)
     cheat
     qabbrev_tac `ff = (specialize (SKOLEM (n' + 1) f))` >>
     
  >- fs[SKOLEM_def,feval_def] >> 
   



     
     `∃M σ. feval M σ (SKOLEM (n' + 1) f)` by cheat >>
     `∃M σ. feval M σ f` by metis_tac[] >>
     map_every qexists_tac [`M''`,`σ''`,`(σ'' n)`] >> rw[]
    



  Induct_on `f` >> fs[qfree_def,SKOLEM_def]

cheat >> 

 fs[PULL_FORALL] >> Cases_on `f` >> 




  simp[SKOLEM_def,size_def,feval_def] >> rw[]
QED

``!ff M σ. feval M σ ff ==> ?M' σ'. feval M' σ' (fsubst V⦇n ↦ a⦈ ff)``
rw[feval_fsubst]











val _ = export_theory();

