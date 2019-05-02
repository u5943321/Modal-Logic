open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory relationTheory arithmeticTheory set_relationTheory
     numpairTheory nlistTheory listTheory rich_listTheory pairTheory;
open FOLSyntaxTheory;

val _ = ParseExtras.tight_equality()


val _ = new_theory "FOLModel";


val _ = Datatype`
        folmodel = <| dom : 'a set ;
                      fnsyms : num -> 'a list -> 'a;
                      predsyms : num -> 'a -> bool;
                      relsyms : num -> 'a -> 'a -> bool;
                      |>`;

val wffm_def = Define`
  wffm M <=> (!k l. (!a. MEM a l ==> a IN M.dom) ==> M.fnsyms k l IN M.dom) /\
             M.dom <> {}`;

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


Theorem UPDATE_tsubst :
 !M σ a n. interpret M σ (tsubst V⦇n ↦ a⦈ t) = (interpret M σ⦇n ↦ interpret M σ a⦈ t)
Proof 
 completeInduct_on `fterm_size t` >> rw[] >> Cases_on `t` >> rw[tsubst_def,interpret_def]
 (* 2 *)
 >- (Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def])
 >- (simp[MAP_MAP_o] >> AP_TERM_TAC >> irule LIST_EQ >> rw[EL_MAP] >> 
    first_x_assum irule >> qexists_tac `fterm_size (EL x l)` >> rw[fterm_size_def] >>
    `fterm_size (EL x l) < fterm1_size l` suffices_by fs[] >> irule tsize_lemma >>
    fs[EL_MEM])
QED


Theorem interpret_tfns :
  !t M1 M2 σ. M1.dom = M2.dom /\ 
              (!fc. fc IN (tfns t) ==> M1.fnsyms (FST fc) = M2.fnsyms (FST fc)) /\
              M1.predsyms = M2.predsyms /\
              M1.relsyms = M2.relsyms /\ IMAGE σ (univ(:num)) ⊆ M1.dom ==>
              (interpret M1 σ t = interpret M2 σ t)
Proof
  completeInduct_on `fterm_size t` >> rw[] >> Cases_on `t` >> rw[interpret_def] >>
  fs[tfns_def] >> `FST (n,LENGTH l) = n` by fs[] >> 
  `M1.fnsyms n = M2.fnsyms n` by metis_tac[] >> rw[] >>
  `(MAP (λa. interpret M1 σ a) l) = (MAP (λa. interpret M2 σ a) l)` 
    suffices_by metis_tac[] >>
  irule MAP_LIST_EQ >> rw[] >> first_x_assum irule >> rw[] (* 2 *)
  >- (first_x_assum irule >> 
     `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l)` suffices_by metis_tac[] >>
     qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])
  >- (`fterm_size m < fterm1_size l` suffices_by fs[] >> rw[tsize_lemma])
QED



Theorem feval_ffns :
  !f M1 M2 σ. M1.dom = M2.dom /\ 
              (!fc. fc IN (ffns f) ==> M1.fnsyms (FST fc) = M2.fnsyms (FST fc)) /\
              M1.predsyms = M2.predsyms /\
              M1.relsyms = M2.relsyms /\ IMAGE σ (univ(:num)) ⊆ M1.dom ==>
              (feval M1 σ f <=> feval M2 σ f)
Proof
  Induct_on `f` >> rw[feval_def] (* 5 *)
  >- (Cases_on `f` >> Cases_on `f0` >> rw[interpret_def] (* 3 *)
     >- (fs[ffns_def,tfns_def] >>
        `M1.fnsyms n'' = M2.fnsyms n''` by
          (`n'' = FST (n'',LENGTH l)` by fs[] >> 
           `M1.fnsyms (FST (n'',LENGTH l)) = M2.fnsyms (FST (n'',LENGTH l))` suffices_by
             metis_tac[] >> first_x_assum irule >> rw[]) >> fs[] >>
        `(MAP (λa. interpret M1 σ a) l) = (MAP (λa. interpret M2 σ a) l)` 
          suffices_by metis_tac[] >> irule MAP_LIST_EQ >> rw[] >> 
        `(∀fc. fc ∈ tfns m ⇒ M1.fnsyms (FST fc) = M2.fnsyms (FST fc))` suffices_by 
          metis_tac[interpret_tfns] >>
        rw[] >> first_x_assum irule >> 
        `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l)` suffices_by metis_tac[] >>
        qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])
     >- (fs[ffns_def,tfns_def] >> 
        `M1.fnsyms n' = M2.fnsyms n'` by
          (`n' = FST (n',LENGTH l)` by fs[] >> 
           `M1.fnsyms (FST (n',LENGTH l)) = M2.fnsyms (FST (n',LENGTH l))` suffices_by
             metis_tac[] >> first_x_assum irule >> rw[]) >> fs[] >>
        `(MAP (λa. interpret M1 σ a) l) = (MAP (λa. interpret M2 σ a) l)` 
          suffices_by metis_tac[] >> irule MAP_LIST_EQ >> rw[] >> 
        `(∀fc. fc ∈ tfns m ⇒ M1.fnsyms (FST fc) = M2.fnsyms (FST fc))` suffices_by 
          metis_tac[interpret_tfns] >>
        rw[] >> first_x_assum irule >> 
        `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l)` suffices_by metis_tac[] >>
        qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])
     >- (fs[ffns_def,tfns_def] >> 
        `M1.fnsyms n' = M2.fnsyms n'` by
          (`n' = FST (n',LENGTH l)` by fs[] >> 
           `M1.fnsyms (FST (n',LENGTH l)) = M2.fnsyms (FST (n',LENGTH l))` suffices_by
             metis_tac[] >> first_x_assum irule >> rw[]) >> fs[] >>
        `M1.fnsyms n'' = M2.fnsyms n''` by
          (`n'' = FST (n'',LENGTH l')` by fs[] >> 
           `M1.fnsyms (FST (n'',LENGTH l')) = M2.fnsyms (FST (n'',LENGTH l'))` suffices_by
             metis_tac[] >> first_x_assum irule >> rw[]) >> fs[] >>
         `(MAP (λa. interpret M1 σ a) l') = (MAP (λa. interpret M2 σ a) l') /\
          (MAP (λa. interpret M1 σ a) l) = (MAP (λa. interpret M2 σ a) l)` 
          suffices_by metis_tac[] >> rw[] (* 2 *)
         >- (irule MAP_LIST_EQ >> rw[] >> 
            `(∀fc. fc ∈ tfns m ⇒ M1.fnsyms (FST fc) = M2.fnsyms (FST fc))` suffices_by 
            metis_tac[interpret_tfns] >>
            rw[] >> first_x_assum irule >> 
            `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l')` suffices_by metis_tac[] >>
            qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])
         >- (irule MAP_LIST_EQ >> rw[] >> 
            `(∀fc. fc ∈ tfns m ⇒ M1.fnsyms (FST fc) = M2.fnsyms (FST fc))` suffices_by 
            metis_tac[interpret_tfns] >>
            rw[] >> first_x_assum irule >> 
            `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l)` suffices_by metis_tac[] >>
            qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])))
  >- (Cases_on `f` >> rw[interpret_def] >> 
     fs[ffns_def,tfns_def] >> 
     `M1.fnsyms n' = M2.fnsyms n'` by
      (`n' = FST (n',LENGTH l)` by fs[] >> 
       `M1.fnsyms (FST (n',LENGTH l)) = M2.fnsyms (FST (n',LENGTH l))` suffices_by
         metis_tac[] >> first_x_assum irule >> rw[]) >> fs[] >>
     `(MAP (λa. interpret M1 σ a) l) = (MAP (λa. interpret M2 σ a) l)` 
          suffices_by metis_tac[] >> irule MAP_LIST_EQ >> rw[] >> 
     `(∀fc. fc ∈ tfns m ⇒ M1.fnsyms (FST fc) = M2.fnsyms (FST fc))` suffices_by 
       metis_tac[interpret_tfns] >>
     rw[] >> first_x_assum irule >> 
     `∃s. fc ∈ s ∧ MEM s (MAP (λa'. tfns a') l)` suffices_by metis_tac[] >>
     qexists_tac `tfns m` >> rw[MEM_MAP] >> metis_tac[])
  >- (fs[ffns_def] >> metis_tac[])
  >> (fs[ffns_def] >> rw[EQ_IMP_THM] (* 2 same *)
     >> first_x_assum drule >> rw[] >>
        `(feval M1 σ⦇n ↦ x⦈ f ⇔ feval M2 σ⦇n ↦ x⦈ f)` suffices_by metis_tac[] >>
        first_x_assum irule >> rw[] >> metis_tac[UPDATE_IMAGE])       
QED


Theorem feval_fsubst_interpret :
  !f M σ a n. (feval M σ (fsubst V(|n |-> a|) f) <=> feval M σ(|n |-> interpret M σ a|) f)
Proof
  rw[feval_fsubst] >> irule feval_ffvs >> rw[] >>
  Cases_on `n = n'` >> fs[APPLY_UPDATE_THM,interpret_def]
QED

Theorem FST_tfns_LESS_num_of_term:
  !a fc. fc IN tfns a ==> FST fc < num_of_term a 
Proof
  completeInduct_on `fterm_size a` >> Cases_on `a` >> fs[tfns_def] >> rw[] 
  >- (simp[FST,num_of_term_def] >>
     `n <= 2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l)` suffices_by fs[] >>
     `n ⊗ nlist_of (MAP (λa. num_of_term a) l) <= 
      2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[] >>
     `n <= n ⊗ nlist_of (MAP (λa. num_of_term a) l)` 
       suffices_by metis_tac[LESS_EQ_TRANS] >> metis_tac[nfst_le_npair]) >>
  Cases_on `fc` >> simp[num_of_term_def] >> 
  `q <= 2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l)` suffices_by fs[] >>
  `n ⊗ nlist_of (MAP (λa. num_of_term a) l) <= 
   2 * n ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[] >>
  `q <= n ⊗ nlist_of (MAP (λa. num_of_term a) l)` 
      suffices_by metis_tac[LESS_EQ_TRANS] >> 
  fs[MEM_MAP] >> rw[] >> 
  `q <= nlist_of (MAP (λa. num_of_term a) l)` 
   suffices_by metis_tac[nsnd_le_npair,LESS_EQ_TRANS] >>
  `?a. MEM a (MAP (λa. num_of_term a) l) /\ q <= a` 
   suffices_by (rw[] >> drule MEM_nlist_of_LESS >> rw[]) >>
  qexists_tac `num_of_term a'` >> simp[MEM_MAP,PULL_EXISTS] >> 
  qexists_tac `a'` >> rw[] >> 
  `q < num_of_term a'` suffices_by fs[] >>
  `(q = FST (q,r))` by metis_tac[FST] >> 
  `FST (q,r) < num_of_term a'` suffices_by metis_tac[] >>
  first_x_assum irule >> rw[] >> 
  `fterm_size a' < fterm1_size l` suffices_by fs[] >> metis_tac[tsize_lemma] 
QED



Theorem ffns_LESS_num_of_term :
  !f fc. fc IN ffns f ==> FST fc < num_of_form f
Proof
  Induct_on `f` >> rw[num_of_form_def] >> fs[ffns_def,tfvs_def] (* 7 *)
  >- (Cases_on `f` >> fs[tfns_def] (* 2 *)
     >- (`n' <= 5 * n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` suffices_by fs[] >>
        `n' <= n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` suffices_by fs[] >>
        `num_of_term (Fn n' l) ⊗ num_of_term f0 <=
         n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` by fs[nsnd_le_npair] >>
        `num_of_term (Fn n' l) <= num_of_term (Fn n' l) ⊗ num_of_term f0`
          by fs[nfst_le_npair] >>
        `num_of_term (Fn n' l) <= 
         n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` by metis_tac[LESS_EQ_TRANS] >>
        `n' <= num_of_term (Fn n' l)` suffices_by fs[] >> rw[num_of_term_def] >>
        `n' <= 2 * n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` suffices_by fs[] >>
        `n' <= n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[nfst_le_npair] >>
        `n' ⊗ nlist_of (MAP (λa. num_of_term a) l) <=
         2 * n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[] >> 
        metis_tac[LESS_EQ_TRANS])
     >- (`FST fc <= 5 * n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` suffices_by fs[] >>
        `FST fc <= n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` suffices_by fs[] >>
        `num_of_term (Fn n' l) ⊗ num_of_term f0 <=
         n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` by fs[nsnd_le_npair] >>
        `num_of_term (Fn n' l) <= num_of_term (Fn n' l) ⊗ num_of_term f0`
          by fs[nfst_le_npair] >>
        `num_of_term (Fn n' l) <= 
         n ⊗ num_of_term (Fn n' l) ⊗ num_of_term f0` by metis_tac[LESS_EQ_TRANS] >>
        `FST fc <= num_of_term (Fn n' l)` suffices_by fs[] >> rw[num_of_term_def] >>
        `FST fc ≤ 2 * n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` suffices_by fs[] >>
        `FST fc ≤ n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` suffices_by fs[] >>
        `nlist_of (MAP (λa. num_of_term a) l) <=
         n' ⊗ nlist_of (MAP (λa. num_of_term a) l)` by fs[nsnd_le_npair] >>
        `FST fc ≤ nlist_of (MAP (λa. num_of_term a) l)`
          suffices_by metis_tac[LESS_EQ_TRANS] >>
        fs[MEM_MAP] >> rw[] >> 
        `?a. MEM a (MAP (λa. num_of_term a) l) /\ FST fc <= a`
          suffices_by (rw[] >> drule MEM_nlist_of_LESS >> rw[]) >>
        rw[MEM_MAP,PULL_EXISTS] >> qexists_tac `a'` >> rw[] >> 
        drule FST_tfns_LESS_num_of_term >> fs[]))
  >- (Cases_on `fc` >> fs[FST] >> 
     `q <= 5 * n ⊗ num_of_term f ⊗ num_of_term f0` suffices_by fs[] >>
     `n ⊗ num_of_term f ⊗ num_of_term f0 <=
      5 * n ⊗ num_of_term f ⊗ num_of_term f0` by fs[] >>
     irule LESS_EQ_TRANS >> qexists_tac `n ⊗ num_of_term f ⊗ num_of_term f0`>>
     rw[] >> 
     `num_of_term f ⊗ num_of_term f0 <= 
      n ⊗ num_of_term f ⊗ num_of_term f0` by fs[nsnd_le_npair] >>
     `num_of_term f0 <= num_of_term f ⊗ num_of_term f0` by fs[nsnd_le_npair] >>
     `q <= num_of_term f0` suffices_by metis_tac[LESS_EQ_TRANS] >>
     `q < num_of_term f0` suffices_by fs[] >>
     drule FST_tfns_LESS_num_of_term >> simp[FST])
  >- (Cases_on `fc` >> fs[FST] >> 
     `q <= 5 * n ⊗ num_of_term f` suffices_by fs[] >>
     `n ⊗ num_of_term f <= 5 * n ⊗ num_of_term f` by fs[] >>
     irule LESS_EQ_TRANS >> qexists_tac `n ⊗ num_of_term f` >> rw[] >>
     `num_of_term f <= n ⊗ num_of_term f` by fs[nsnd_le_npair] >>
     `q <= num_of_term f` suffices_by metis_tac[LESS_EQ_TRANS] >>
     `q < num_of_term f` suffices_by fs[] >>
     drule FST_tfns_LESS_num_of_term >> simp[FST])
  >- (first_x_assum drule >> rw[] >>
     `num_of_form f < 5 * num_of_form f ⊗ num_of_form f' + 3` 
      suffices_by metis_tac[LESS_TRANS] >>
     `num_of_form f <= 5 * num_of_form f ⊗ num_of_form f'` 
      suffices_by fs[] >>
     `num_of_form f <= num_of_form f ⊗ num_of_form f'` by fs[nfst_le_npair] >>
     `num_of_form f ⊗ num_of_form f' <=
      5 * num_of_form f ⊗ num_of_form f'` by fs[] >>
     metis_tac[LESS_EQ_TRANS])
  >- (first_x_assum drule >> rw[] >>
     `num_of_form f' < 5 * num_of_form f ⊗ num_of_form f' + 3` 
      suffices_by metis_tac[LESS_TRANS] >>
     `num_of_form f' <= 5 * num_of_form f ⊗ num_of_form f'` 
      suffices_by fs[] >>
     `num_of_form f' <= num_of_form f ⊗ num_of_form f'` by fs[nsnd_le_npair] >>
     `num_of_form f ⊗ num_of_form f' <=
      5 * num_of_form f ⊗ num_of_form f'` by fs[] >>
     metis_tac[LESS_EQ_TRANS])
  >- (first_x_assum drule >> rw[] >>
     `num_of_form f < 5 * n ⊗ num_of_form f + 4` 
      suffices_by metis_tac[LESS_TRANS] >>
     `num_of_form f <= 5 * n ⊗ num_of_form f` 
      suffices_by fs[] >>
     `num_of_form f <= n ⊗ num_of_form f` by fs[nsnd_le_npair] >>
     `n ⊗ num_of_form f <= 5 * n ⊗ num_of_form f` by fs[] >>
     metis_tac[LESS_EQ_TRANS])
  >- (first_x_assum drule >> rw[] >>
     `num_of_form f < 5 * n ⊗ num_of_form f + 5` 
      suffices_by metis_tac[LESS_TRANS] >>
     `num_of_form f <= 5 * n ⊗ num_of_form f` 
      suffices_by fs[] >>
     `num_of_form f <= n ⊗ num_of_form f` by fs[nsnd_le_npair] >>
     `n ⊗ num_of_form f <= 5 * n ⊗ num_of_form f` by fs[] >>
     metis_tac[LESS_EQ_TRANS])
QED



Theorem prenex_original_implies_SKOLEM :
  !f. prenex f ==> !M:'a folmodel σ. fsatis M σ f /\ M.dom <> {} ==> 
                       !n. ?M:'a folmodel σ. fsatis M σ (specialize (SKOLEM n f))
Proof
completeInduct_on `size f` >>
`∀f.
       prenex f ⇒ v = size f ⇒
       ∀M:'a folmodel σ. fsatis M σ f /\ M.dom <> {}⇒
          ∀n. ∃M:'a folmodel σ. fsatis M σ (specialize (SKOLEM n f))` 
  suffices_by metis_tac[] >>
Induct_on `prenex f` >> rw[SKOLEM_def,SKOLEM_qfree,specialize_qfree]
>- metis_tac[]
>- (qabbrev_tac `a = Fn ((n ⊗ num_of_form f) ⊗ n')
                    (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))` >>
   fs[fsatis_def,feval_def] >>
   last_x_assum irule >> rw[] (* 2 *)
   >- rw[GSYM size_fsubst,size_def]
   >- (rw[feval_fsubst_interpret] >> 
      qexists_tac `<| dom := M.dom ;
                        fnsyms := λ m l. 
                                (if m = ((n ⊗ num_of_form f) ⊗ n') /\ 
l = (MAP (λa. interpret M σ a) (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))) then x else (M.fnsyms m l));
                      predsyms := M.predsyms;
                      relsyms := M.relsyms;
                      |>` >> 
      qexists_tac `σ` >> rw[] >>
      qmatch_abbrev_tac `feval M0 _ f` >>
      `interpret M0 σ a = x` by
        (simp[Abbr`a`,interpret_def] >> 
         `(MAP (λa. interpret M0 σ a) (MAP V (SET_TO_LIST (ffvs (fEXISTS n f))))) = 
          (MAP (λa. interpret M σ a) (MAP V (SET_TO_LIST (ffvs (fEXISTS n f)))))`
            suffices_by (rw[] >> rw[Abbr`M0`]) >>
         irule MAP_LIST_EQ >> rw[MEM_MAP] >> 
         irule interpret_tfns >> rw[] (* 5 *)
         >- fs[tfns_def]
         >> fs[Abbr`M0`]) >> fs[] >>
      `feval M σ⦇n ↦ x⦈ f = feval M0 σ⦇n ↦ x⦈ f` suffices_by metis_tac[] >>
      irule feval_ffns >> rw[] (* 5 *)
      >- (`FST fc <> (n ⊗ num_of_form f) ⊗ n'` by
            (strip_tac >> 
             `(n ⊗ num_of_form f) <= (n ⊗ num_of_form f) ⊗ n'` by fs[nfst_le_npair] >>
             `num_of_form f <= n ⊗ num_of_form f` by fs[nsnd_le_npair] >>
             `num_of_form f <= FST fc` by metis_tac[LESS_EQ_TRANS] >>
             `FST fc < num_of_form f` suffices_by fs[] >>
             metis_tac[ffns_LESS_num_of_term]) >>
           fs[Abbr`M0`] >> rw[FUN_EQ_THM])
       >> fs[Abbr`M0`]
       >- (irule UPDATE_IMAGE >> rw[])))
>- (rw[specialize_def] >> 
   first_x_assum (qspec_then `size f` mp_tac) >> rw[] >> fs[size_def] >>
   first_x_assum (qspec_then `f` mp_tac) >> rw[] >> first_x_assum irule >>
   fs[fsatis_def,feval_def] >> fs[GSYM MEMBER_NOT_EMPTY] >> 
   metis_tac[UPDATE_IMAGE])
QED


 
Theorem IMAGE_NOT_EMPTY :
  !f A B. IMAGE f A ⊆ B /\ A <> {} ==> B <> {}
Proof
  rw[IMAGE_DEF] >> strip_tac >> fs[] >> fs[EXTENSION] >> metis_tac[]
QED



Theorem interpret_IN_dom :
  (∀M:α folmodel k l. M.fnsyms k l ∈ M.dom) ==> !M:α folmodel σ. IMAGE σ 𝕌(:num) ⊆ M.dom ==>
  !a. (interpret M σ a) IN M.dom
Proof
  rw[] >> Cases_on `a` >> rw[interpret_def]
  >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[]
QED


Theorem universal_feval_fsubst :
  !f v M.(!M:α folmodel. (!k l. (M.fnsyms k l) IN M.dom)) ==>
          ((!σ. IMAGE σ univ(:num) ⊆ M.dom ==> feval M σ f) <=> 
          (!σ. IMAGE σ univ(:num) ⊆ M.dom ==> !a. (interpret M σ a) IN M.dom 
               ==> feval M σ (fsubst V(|n |-> a|) f)))
Proof
  rw[EQ_IMP_THM] 
  >- (simp[feval_fsubst_interpret] >> 
     `IMAGE σ⦇n ↦ interpret M σ a⦈ univ(:num) ⊆ M.dom` suffices_by metis_tac[]>>
     metis_tac[UPDATE_IMAGE])
  >- (`(fsubst V⦇n ↦ V n⦈ f) = f`
       by (`V⦇n ↦ V n⦈ = V` suffices_by metis_tac[fsubst_V] >> 
           simp[FUN_EQ_THM] >> strip_tac >> 
           Cases_on `n = x` >> fs[APPLY_UPDATE_THM]) >>
     `feval M σ (fsubst V⦇n ↦ V n⦈ f)` suffices_by metis_tac[] >>
     first_x_assum irule >> fs[interpret_def,SUBSET_DEF] >> metis_tac[]) 
QED

Theorem interpret_idempotent :
  !M σ t. (interpret M (interpret M σ ∘ V) t) = interpret M σ t
Proof
  completeInduct_on `fterm_size t` >> Cases_on `t`
  >- rw[interpret_def] >>
  rw[interpret_def] >> AP_TERM_TAC >> irule MAP_LIST_EQ >> rw[] >>
  first_x_assum irule >> qexists_tac `fterm_size m` >> rw[] >>
  drule tsize_lemma >> rw[]
QED

Theorem feval_interpret :
  !f M σ. feval M (interpret M σ ∘ V) f = feval M σ f
Proof
Induct_on `f` >> rw[feval_def,interpret_idempotent] (* 2 *)
>> (`∀x. x ∈ M.dom ⇒ feval M (interpret M σ ∘ V)⦇n ↦ x⦈ f = feval M σ⦇n ↦ x⦈ f`
     suffices_by metis_tac[] >> rw[] >> irule feval_ffvs >> rw[] >>
   Cases_on `(n = n')` >> fs[APPLY_UPDATE_THM,interpret_def])
QED

Theorem universal_fsubst :
  (∀M:α folmodel k l. M.fnsyms k l ∈ M.dom) ==>
    !M:α folmodel. M.dom <> {} ==>
       !f. 
         (!σ. IMAGE σ univ(:num) ⊆ M.dom ==> feval M σ f) <=>
         (!v σ. 
            (IMAGE σ univ(:num) ⊆ M.dom /\ IMAGE (interpret M σ) (IMAGE v univ(:num)) ⊆ M.dom) ==> feval M σ (fsubst v f))
Proof
strip_tac >> strip_tac >> strip_tac >> Induct_on `f` (* 6 *)
>- (fs[feval_def,fsubst_def] >> rw[EQ_IMP_THM] >> SPOSE_NOT_THEN ASSUME_TAC >>
   `∀v σ.
        (IMAGE σ 𝕌(:num) ⊆ M.dom) ==>
            ¬(IMAGE (interpret M σ) (IMAGE v 𝕌(:num)) ⊆ M.dom)`by metis_tac[]>>
   `∀σ.
      (IMAGE σ 𝕌(:num) ⊆ M.dom) ==>
         !v.¬(IMAGE (interpret M σ) (IMAGE v 𝕌(:num)) ⊆ M.dom)`by metis_tac[]>>
   first_x_assum drule >> strip_tac >>
   fs[GSYM MEMBER_NOT_EMPTY] >>
   `?v. (IMAGE (interpret M σ) (IMAGE v 𝕌(:num)) ⊆ M.dom)`
     suffices_by metis_tac[] >> 
   qexists_tac `v` >> 
   Q.UNDISCH_THEN `∀v. ¬(IMAGE (interpret M σ) (IMAGE v 𝕌(:num)) ⊆ M.dom)` (K ALL_TAC) >>
   Q.UNDISCH_THEN `∀v σ.
             IMAGE σ 𝕌(:num) ⊆ M.dom ⇒
             ¬(IMAGE (interpret M σ) (IMAGE v 𝕌(:num)) ⊆ M.dom)` (K ALL_TAC) >>
   rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[])
>- (fs[feval_def,fsubst_def] >> rw[EQ_IMP_THM] (* 2 *)
   >- (simp[interpret_tsubst] >> 
      `IMAGE (interpret M σ ∘ v) 𝕌(:num) ⊆ M.dom` suffices_by metis_tac[] >>
      rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[])
   >- (`?v σ0.
             IMAGE σ0 𝕌(:num) ⊆ M.dom ∧
             IMAGE (interpret M σ0) (IMAGE v 𝕌(:num)) ⊆ M.dom /\
             M.relsyms n (interpret M σ0 (tsubst v f))
               (interpret M σ0 (tsubst v f0)) = M.relsyms n (interpret M σ f) (interpret M σ f0)` suffices_by metis_tac[] >>
      map_every qexists_tac [`V`,`σ`] >> rw[tsubst_V,IMAGE_DEF,SUBSET_DEF] >> 
      irule interpret_IN_dom >> rw[]))
>- (fs[feval_def,fsubst_def] >> rw[EQ_IMP_THM] (* 2 *)
   >- (fs[interpret_tsubst] >> first_x_assum irule >>
      rw[tsubst_V,IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[])
   >- (`?v σ0.
             IMAGE σ0 𝕌(:num) ⊆ M.dom ∧
             IMAGE (interpret M σ0) (IMAGE v 𝕌(:num)) ⊆ M.dom /\
             (M.predsyms n (interpret M σ0 (tsubst v f)) = 
              M.predsyms n (interpret M σ f))` suffices_by metis_tac[] >>
      map_every qexists_tac [`V`,`σ`] >> rw[tsubst_V,IMAGE_DEF,SUBSET_DEF] >>
      irule interpret_IN_dom >> rw[]))
>- (fs[feval_def,fsubst_def] >> rw[EQ_IMP_THM] (* 2 *)
   >- (fs[feval_fsubst] >> first_x_assum irule >> rw[IMAGE_DEF,SUBSET_DEF] >>
      irule interpret_IN_dom >> rw[])
   >- (`?v σ0.
             IMAGE σ0 𝕌(:num) ⊆ M.dom ∧
             IMAGE (interpret M σ0) (IMAGE v 𝕌(:num)) ⊆ M.dom /\
             feval M σ0 (fsubst v f) /\
             (feval M σ0 (fsubst v f') = feval M σ f')`suffices_by metis_tac[]>>
      map_every qexists_tac [`V`,`σ`] >> rw[fsubst_V,IMAGE_DEF,SUBSET_DEF] >>
      irule interpret_IN_dom >> rw[]))
>- (fs[feval_def] >> rw[EQ_IMP_THM] (* 2 *)
   >- (rw[feval_fsubst,feval_def] >> first_x_assum irule >> 
      rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[])
   >- (`?v σ0.
             IMAGE σ0 𝕌(:num) ⊆ M.dom ∧
             IMAGE (interpret M σ0) (IMAGE v 𝕌(:num)) ⊆ M.dom /\
             (feval M σ0 (fsubst v (fFORALL n f)) ==> feval M σ⦇n ↦ x⦈ f)`
        suffices_by metis_tac[] >>
      rw[feval_fsubst,feval_def] >>
      map_every qexists_tac[`V`,`σ`] >> rw[feval_interpret] (* 2 *)
      >- (rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[]) >>
      `feval M (interpret M σ ∘ V)⦇n ↦ x⦈ f` by metis_tac[] >>
      `(feval M (interpret M σ ∘ V)⦇n ↦ x⦈ f = feval M σ⦇n ↦ x⦈ f)`
        suffices_by metis_tac[] >> irule feval_ffvs >> rw[] >>
      Cases_on `(n = n')` >> fs[APPLY_UPDATE_THM,interpret_def]))
>- (fs[feval_def] >> rw[EQ_IMP_THM] (* 2 *)
   >- (rw[feval_fsubst,feval_def] >> first_x_assum irule >> 
      rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[]) >>
   fs[feval_fsubst,feval_def] >> 
   first_x_assum (qspec_then `V` mp_tac) >> strip_tac >>
   first_x_assum (qspec_then `σ` mp_tac) >> strip_tac >>
   `IMAGE (interpret M σ) (IMAGE V 𝕌(:num)) ⊆ M.dom` by 
     (rw[IMAGE_DEF,SUBSET_DEF] >> irule interpret_IN_dom >> rw[]) >>
   first_x_assum drule >> rw[] >> qexists_tac `x` >> rw[] >>
   `(feval M (interpret M σ ∘ V)⦇n ↦ x⦈ f = feval M σ⦇n ↦ x⦈ f)` 
     suffices_by metis_tac[] >> irule feval_ffvs >> rw[] >>
   Cases_on `(n = n')` >> rw[APPLY_UPDATE_THM,interpret_def])
QED


Theorem universal_fFORALL :
  (∀M:α folmodel k l. M.fnsyms k l ∈ M.dom) ⇒
     ∀M:α folmodel.
         M.dom ≠ ∅ ⇒
         ∀f.
             (∀σ. IMAGE σ 𝕌(:num) ⊆ M.dom ⇒ feval M σ f) ⇔
             (∀σ n.
                 IMAGE σ 𝕌(:num) ⊆ M.dom ==> feval M σ (fFORALL n f)) 
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (drule (universal_feval_fsubst|> INST_TYPE [gamma |-> ``:'a``]) >> rw[] >>  
    first_x_assum (qspecl_then [`f`,`M`] assume_tac) >> 
    rw[feval_def] >> fs[feval_fsubst_interpret] >> 
    qabbrev_tac `(σ0 = σ⦇n ↦ x⦈)` >>
    `(x = interpret M σ0 (V n))` by
      rw[Abbr`σ0`,interpret_def,APPLY_UPDATE_THM] >>
    last_x_assum (qspec_then `σ0` assume_tac) >> 
    `IMAGE σ0 𝕌(:num) ⊆ M.dom`
      by (rw[Abbr`σ0`] >> metis_tac[UPDATE_IMAGE]) >>
    `interpret M σ0 (V n) ∈ M.dom` by metis_tac[] >>
    first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
    `(feval M σ0⦇n ↦ interpret M σ0 (V n)⦈ f = feval M σ0 f)` suffices_by
     metis_tac[] >>
    irule feval_ffvs >> rw[] >> Cases_on `(n = n')` >>
    fs[APPLY_UPDATE_THM,interpret_def])
>- (fs[feval_def] >> 
   `?σ' n x.
             IMAGE σ' 𝕌(:num) ⊆ M.dom /\ x ∈ M.dom /\
             (feval M σ'⦇n ↦ x⦈ f = feval M σ f)` suffices_by metis_tac[] >>
   map_every qexists_tac [`σ`,`n`,`σ n`] >> fs[IMAGE_DEF,SUBSET_DEF] >> rw[]
   >- metis_tac[] >>
   irule feval_ffvs >> rw[] >> Cases_on `(n = n')` >> fs[APPLY_UPDATE_THM])
QED


Theorem universal_specialize :
  (∀M:α folmodel k l. M.fnsyms k l ∈ M.dom) ⇒
     ∀M:α folmodel.
         M.dom ≠ ∅ ⇒
         ∀f.
             (∀σ. IMAGE σ 𝕌(:num) ⊆ M.dom ⇒ feval M σ f) ⇔
             (∀σ n.
                 IMAGE σ 𝕌(:num) ⊆ M.dom ==> feval M σ (specialize f))
Proof
rw[EQ_IMP_THM]
>- (Induct_on `f` >> rw[specialize_def,feval_def] >- metis_tac[] >>
   first_x_assum irule >> rw[] >>
   `?σ x. IMAGE σ 𝕌(:num) ⊆ M.dom /\ x ∈ M.dom /\ 
    (feval M σ⦇n ↦ x⦈ f = feval M σ' f)` suffices_by metis_tac[] >>
   map_every qexists_tac [`σ'`,`σ' n`] >> rw[] 
   >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
   irule feval_ffvs >> rw[] >> Cases_on `(n = n')` >> fs[APPLY_UPDATE_THM])
>- (`!σ. IMAGE σ 𝕌(:num) ⊆ M.dom ==> feval M σ f` suffices_by metis_tac[] >>
   Induct_on `f`
   >- fs[specialize_def] 
   >- fs[specialize_def] 
   >- fs[specialize_def] 
   >- fs[specialize_def]
   >- (drule universal_fFORALL >> strip_tac >> strip_tac >> strip_tac >>
      `(∀σ. IMAGE σ 𝕌(:num) ⊆ M.dom ⇒ feval M σ f)` suffices_by metis_tac[] >>
      fs[specialize_def])
   >- fs[feval_def,specialize_def])
QED


val SKOLEM_ffns_def = Define
  `SKOLEM_ffns n (fFALSE) = {} /\
   SKOLEM_ffns n (fP a t) = {} /\
   SKOLEM_ffns n (fR a t1 t2) = {} /\
   SKOLEM_ffns n (fIMP f1 f2) = SKOLEM_ffns n f1 ∪ SKOLEM_ffns n f2 /\
   SKOLEM_ffns n (fFORALL m f) = SKOLEM_ffns n f /\
   SKOLEM_ffns n (fEXISTS m f) = SKOLEM_ffns (n+1) f ∪ {npair (npair m (num_of_form f)) n}`;





val SKOLEM_folmodel_def = Define`
  SKOLEM_folmodel M ffs = 
  <| dom := M.dom ;
     fnsyms := λ g zs.
     if (?ff. ff IN ffs /\ g IN (SKOLEM_ffns 0 ff)) /\
        (LENGTH zs = 
        CARD 
          (ffvs 
            (fEXISTS (nfst (nfst g)) (form_of_num (nsnd (nfst g))))))
     then (@a. a IN M.dom /\ 
          feval M 
                ((λ(n,w) σ. σ(|n |-> w|))
                   (nfst (nfst g),a) 
                   (FOLDR 
                      (λ(n,w) σ. σ(|n |-> w|))
                      (λz. @c. c IN M.dom)
                      (MAP2 
                         (\n w. (n,w)) 
                         (SET_TO_LIST 
                            (ffvs 
                              (fEXISTS (nfst (nfst g)) 
                                      (form_of_num (nsnd (nfst g))) ))) 
                         zs)))
                (form_of_num (nsnd (nfst g))))
     else M.fnsyms g zs;
     predsyms := M.predsyms;
     relsyms := M.relsyms;
  |>`


Theorem SKOLEM_ffns_qfree :
  !f n. qfree f ==> SKOLEM_ffns n f = {}
Proof
  Induct_on `f` >> rw[qfree_def,SKOLEM_ffns_def]
QED

Theorem disjoint_INSERT :
  !a b. a ∩ b = {} ==>
         !c. c NOTIN a ==> a ∩ (b ∪ {c}) = {}
Proof
  rw[] >> 
  fs[EXTENSION] >> metis_tac[]
QED

Theorem prenex_SKOLEM_ffns_disjoint :
  !f1. prenex f1 ==> 
      !f2. prenex f2 ==>
             f1 <> f2 ==>
               !m n. SKOLEM_ffns m f1 ∩ SKOLEM_ffns n f2 = {}
Proof
  Induct_on `prenex f1` >> rw[] (* 3 *)
  >- fs[SKOLEM_ffns_qfree]
  >- `!f2. 
          prenex f2 ==> 
            prenex f1 /\  
            (∀f2. prenex f2 ⇒ !m n. SKOLEM_ffns m f1 ∩ SKOLEM_ffns n f2 = ∅) ==>
              !m n n'. SKOLEM_ffns m (fEXISTS n f1) ∩ SKOLEM_ffns n' f2 = ∅`
       suffices_by metis_tac[] >>
     rpt (pop_assum (K ALL_TAC)) >>      
     Induct_on `prenex f2` >> rw[] (* 3 *)
     >- fs[SKOLEM_ffns_qfree]
     >- last_x_assum drule >> rw[] >> 
        first_x_assum (qspecl_then [`m`,`n'`,`n'' + 1`] assume_tac) >>
        qabbrev_tac`s1 = SKOLEM_ffns m (fEXISTS n' f1)` >>
        simp[SKOLEM_ffns_def] >> irule disjoint_INSERT >> rw[] >>
        simp[Abbr`s1`,SKOLEM_ffns_def] >> rw[]
        >- 
rw[SKOLEM_ffns_def] >> 


Theorem prenex_NOTIN_SKOLEM_ffns :
  !ff. prenex ff ==> 
          !f. f IN (ffns ff) ==> !n. (FST f) NOTIN (SKOLEM_ffns n ff)
Proof
  Induct_on `prenex` >> rw[]
  >- fs[SKOLEM_ffns_qfree]
  >- (fs[SKOLEM_ffns_def,ffns_def] >>
     drule ffns_LESS_num_of_term >> rw[] >>
     `num_of_form ff <= (n ⊗ num_of_form ff)` by fs[nsnd_le_npair] >>
     `n ⊗ num_of_form ff <= (n ⊗ num_of_form ff) ⊗ n'` by fs[nfst_le_npair] >>
     `FST f < (n ⊗ num_of_form ff) ⊗ n'` suffices_by fs[] >>
     irule LESS_LESS_EQ_TRANS >> 
     qexists_tac `num_of_form ff` >> rw[])
  >- fs[SKOLEM_ffns_def,ffns_def]
QED


Theorem SKOLEM_folmodel :
  !ff s. ff IN s ==> !f. f IN (ffns ff) ==> 
         !M. (SKOLEM_folmodel M s).fnsyms (FST f) = M.fnsyms (FST f)


Theorem SKOLEM_folmodel_qfree :
  !f s.
     f IN s ==>
       qfree f ==>
         !M σ. 
            IMAGE σ 𝕌(:num) ⊆ M.dom ==> 
              feval M σ f ==> feval (SKOLEM_folmodel M s) σ f 
Proof
  Induct_on `f` 
  >- rw[feval_def]
  >- rw[] >> 
     `feval (SKOLEM_folmodel M s) σ (fR n f f0) = feval M σ (fR n f f0)`
       suffices_by metis_tac[] >>
     rw[] >>
     `feval (SKOLEM_folmodel M s) σ f = feval M σ f` suffices_by metis_tac[] >>
     irule feval_ffns >> rw[] (* 5 *)
     >- fs[SKOLEM_folmodel_def]
     >- fs[SKOLEM_folmodel_def]
     >- fs[SKOLEM_folmodel_def]
     >- fs[SKOLEM_folmodel_def]
     >- `¬(∃ff. ff ∈ s ∧ FST fc ∈ SKOLEM_ffns 0 ff)`


Theorem SKOLEM_fsatis :
  (∀M:α folmodel k l. M.fnsyms k l ∈ M.dom) ==>
     !s. 
       (!f. f IN s ==> prenex f) ==>
         ((?M:α folmodel. 
            M.dom <> {} /\ 
            (!σ. IMAGE σ univ(:num) ⊆ M.dom ==> 
               !f. f IN s ==>
                  !n. feval M σ (specialize (SKOLEM n f)))) 
         <=>
         (?M:α folmodel. 
            M.dom <> {} /\ 
            (!σ. IMAGE σ univ(:num) ⊆ M.dom ==> 
               !f. f IN s ==> feval M σ f)))
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (drule universal_specialize >> rw[] >> 
   `∀σ.
      IMAGE σ 𝕌(:num) ⊆ M.dom ⇒
        ∀f. f ∈ s ⇒ ∀n. feval M σ (SKOLEM n f)` by metis_tac[] >>
   qexists_tac `M` >> rw[] >> first_x_assum drule >> rw[] >>
   last_x_assum drule >> rw[] >>
   drule prenex_SKOLEM_implies_original >> metis_tac[])
>- qexists_tac `SKOLEM_folmodel M s` >> rw[]
   >- fs[SKOLEM_folmodel_def] >>
   first_x_assum drule >>
   `!f. prenex f ==> f IN s ==> 
        feval (SKOLEM_folmodel M s) σ (specialize (SKOLEM n f))` 
     suffices_by metis_tac[] >>
   Induct_on `prenex f` >> rw[] (* 3 *)
   >- `IMAGE σ 𝕌(:num) ⊆ M.dom` by fs[SKOLEM_folmodel_def] >> 
      last_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
      

val bumpmod_def = Define`
   bumpmod M = M with fnsyms := \k l. if nfst k = 0 then M.fnsyms (nsnd k) l else ARB`;

val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

Theorem bumpmod_interpret :
  !M σ t. (interpret (bumpmod M) σ (bumpterm t)) = interpret M σ t
Proof 
  ho_match_mp_tac (theorem "interpret_ind") >> rw[interpret_def,bumpterm_def] >>
  simp[MAP_MAP_o,combinTheory.o_ABS_R,Cong MAP_CONG'] >> simp[bumpmod_def]
QED

Theorem bumpmod_feval :
  !M f σ. IMAGE σ univ(:num) ⊆ M.dom ==> 
          (feval M σ f <=> 
          feval (bumpmod M) σ (bumpform f))
Proof
  Induct_on `f` >> rw[feval_def,bumpform_def,bumpmod_interpret] (* 4 *)
  >- simp[bumpmod_def]
  >- simp[bumpmod_def]
  >- (rw[EQ_IMP_THM] >>
     `IMAGE σ⦇n ↦ x⦈ 𝕌(:num) ⊆ M.dom` by fs[bumpmod_def,UPDATE_IMAGE] >> 
     first_x_assum drule >> fs[bumpmod_def])
  >- (rw[EQ_IMP_THM,bumpform_def] >>
     `IMAGE σ⦇n ↦ x⦈ 𝕌(:num) ⊆ M.dom` by fs[bumpmod_def,UPDATE_IMAGE] >>
     first_x_assum drule >> rw[] >> qexists_tac `x` >> rw[] >> fs[bumpmod_def])
QED



Theorem bumpform_qfree :
  !f. qfree f ==> qfree (bumpform f)
Proof
  Induct_on `f` >> rw[qfree_def,bumpform_def]
QED 


Theorem bumpterm_nfst_zero:
  !t. fc IN (tfns (bumpterm t)) ==> nfst (FST fc) = 0
Proof
  completeInduct_on `fterm_size t` >> rw[] >> Cases_on `t` >> 
  fs[bumpterm_def,tfns_def] >> fs[MAP_MAP_o,MEM_MAP] >> rw[] >> drule tsize_lemma >>
  rw[] >>
  `fterm_size a < n + (fterm1_size l + 1)` by fs[] >> first_x_assum irule >> 
  metis_tac[] 
QED

Theorem bumpform_nfst_zero :
  !f. fc IN (ffns (bumpform f)) ==> nfst (FST fc) = 0
Proof
  Induct_on `f` >> fs[bumpform_def,ffns_def,bumpterm_nfst_zero] (* 3 *)
  >> metis_tac[bumpterm_nfst_zero]
QED


Theorem SKOLEM_ffns_qfree :
  !f. qfree f ==> !n. SKOLEM_ffns n f = {}
Proof
  Induct_on `f` >> fs[SKOLEM_ffns_def]
QED

Theorem SKOLEM_ffns_nonzero :
  !f. prenex f ==> !fc n. fc IN (SKOLEM_ffns n f) ==> nfst fc <> 0
Proof
  Induct_on `prenex` >> rw[]
  >- metis_tac[SKOLEM_ffns_qfree,MEMBER_NOT_EMPTY]      
  >- fs[SKOLEM_ffns_def]  (* 2 *) >- metis_tac[] >>                                                                                                                                                      

QED

Theorem SKOLEM_bumpform_fsatis :
    !s M:α folmodel. 
      (!f. f IN s ==> prenex f) /\
      wffm M /\ 
      (!σ. IMAGE σ univ(:num) ⊆ M.dom ==>  !f. f IN s ==> feval M σ f)
      ==>
       ?M:α folmodel. 
            wffm M /\ 
            (!σ. IMAGE σ univ(:num) ⊆ M.dom ==> 
               !f. f IN s ==>
                  !n. feval M σ (specialize (SKOLEM n (bumpform f))))
Proof
  rw[] >> qexists_tac `SKOLEM_folmodel (bumpmod M) {bumpform f| f IN s}` >>
  first_x_assum drule >> rpt (pop_assum mp_tac) >>
  `!f. prenex f ==> !n. wffm M ⇒
   (∀σ. IMAGE σ 𝕌(:num) ⊆ M.dom ⇒ ∀f. f ∈ s ⇒ feval M σ f) ⇒
   IMAGE σ 𝕌(:num) ⊆ (SKOLEM_folmodel (bumpmod M) {bumpform f | f ∈ s}).dom ⇒
   f ∈ s ⇒
   feval (SKOLEM_folmodel (bumpmod M) {bumpform f | f ∈ s}) σ
     (specialize (SKOLEM n (bumpform f)))` suffices_by metis_tac[] >>
   Induct_on `prenex f` >> rw[] (* 3 *)
   >- fs[bumpform_qfree,SKOLEM_qfree,specialize_qfree] >> 
      `IMAGE σ 𝕌(:num) ⊆ M.dom` by fs[SKOLEM_folmodel_def,bumpmod_def] >>
      first_x_assum drule_all >> rw[] >>
      `feval (bumpmod M) σ (bumpform f) =
      feval (SKOLEM_folmodel (bumpmod M) {bumpform f | f ∈ s}) σ (bumpform f)`
        suffices_by metis_tac[] >>
     irule feval_ffns >> rw[SKOLEM_folmodel_def] (* 2 *)
     >- rw[FUN_EQ_THM] >> rw[] >> 
        `nfst (FST fc) = 0` by cheat >>
        `nfst 
QED
        
    




`∃M.
       M.dom ≠ ∅ ∧
       ∀σ.
           IMAGE σ 𝕌(:num) ⊆ M.dom ⇒
           ∀f. f ∈ s ⇒ ∀n. feval M σ (SKOLEM n f)` suffices_by 
     (rw[] >> drule universal_specialize >> rw[] >> 
     qexists_tac `M'` >> metis_tac[]) >>
  

QED


val _ = export_theory();

