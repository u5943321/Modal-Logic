open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOLcompactness";


(*

val psatisfiable_def = Define`
  psatisfiable ss (μ:'a itself) (ν:'b itself) = ?M:('a,'b,unit)folmodel σ. (!f. f IN ss ==> fsatis M σ f)`;

val finsat_def = Define`
  finsat ss (μ:'a itself) (ν:'b itself) = (!s0. s0 ⊆ ss /\ FINITE s0 ==> psatisfiable s0 μ ν)`;


val FINITE_chain_SUBSET_lemma = store_thm(
  "FINITE_chain_SUBSET_lemma",
  ``(!A B. A IN U /\ B IN U ==> A ⊆ B \/ B ⊆ A) ==> 

val UNION_finsat_finsat = store_thm(
  "UNION_finsat_finsat",
  ``!U. (!A. A IN U ==> finsat A μ ν) /\ (!A B. A IN U /\ B IN U ==> A ⊆ B \/ B ⊆ A) ==> finsat (BIGUNION U) μ ν``,
  rw[finsat_def,psatisfiable_def,BIGUNION] >>
  `!f. f IN s0 ==> ?s. s IN U /\ f IN s` by (rw[] >> fs[SUBSET_DEF]) >>
  qabbrev_tac `ss = {u | ?f. f IN s0 /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}}` >>
  Cases_on `s0 = {}` >> rw[] >> 
  `(BIGUNION ss) IN U`
      by (rw[Abbr`ss`] >>
         `!s0. FINITE s0 ==>
         s0 SUBSET {x | ?s. s IN U /\ x IN s} /\ (!f. f IN s0 ==> ?s. s IN U /\ f IN s) /\ s0 <> {} ==>
	 BIGUNION {u | ?f. f IN s0 /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} IN U` suffices_by metis_tac[] >>
         Induct_on `FINITE` >> rw[] >> Cases_on `s0' = {}` >> rw[] (* 2 *)
 >- (`{u0 | u0 IN U /\ e IN u0} <> {}`
      by (`?u. u IN {u0 | u0 IN U /\ e IN u0}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
         qexists_tac `s` >> fs[]) >>
    `(CHOICE {u0 | u0 IN U /\ e IN u0}) IN {u0 | u0 IN U /\ e IN u0}` by metis_tac[CHOICE_DEF] >> fs[])
 >- (`(!f. f IN s0' ==> ?s. s IN U /\ f IN s)` by metis_tac[] >>
    `BIGUNION {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} IN U` by metis_tac[] >>
    `BIGUNION {u | ?f. (f = e \/ f IN s0') /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} =
    (CHOICE {u0 | u0 IN U /\ e IN u0}) ∪
    (BIGUNION {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}})`
      by (rw[EXTENSION,EQ_IMP_THM,BIGUNION,PULL_EXISTS] >> metis_tac[]) >>
    `(CHOICE {u0 | u0 IN U /\ e IN u0}) IN U`
      by (`{u0 | u0 IN U /\ e IN u0} <> {}`
            by (`?u. u IN {u0 | u0 IN U /\ e IN u0}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
	       qexists_tac `s` >> fs[]) >>
    `(CHOICE {u0 | u0 IN U /\ e IN u0}) IN {u0 | u0 IN U /\ e IN u0}` by metis_tac[CHOICE_DEF] >> fs[]) >>
    Cases_on `CHOICE {u0 | u0 IN U /\ e IN u0} ⊆
             BIGUNION {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}}`
    >- (`CHOICE {u0 | u0 IN U /\ e IN u0} UNION
       BIGUNION
         {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} =
       BIGUNION
         {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}}` by metis_tac[SUBSET_UNION_ABSORPTION] >>
       metis_tac[])
    >- (`BIGUNION {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} ⊆ CHOICE {u0 | u0 IN U /\ e IN u0}`
       by metis_tac[] >>
       `CHOICE {u0 | u0 IN U /\ e IN u0} UNION
       BIGUNION
         {u | ?f. f IN s0' /\ u = CHOICE {u0 | u0 IN U /\ f IN u0}} = CHOICE {u0 | u0 IN U /\ e IN u0}`
         by metis_tac[SUBSET_UNION_ABSORPTION,UNION_COMM] >> metis_tac[]))) >>
  `s0 ⊆ (BIGUNION ss)`
    by (rw[BIGUNION,SUBSET_DEF,Abbr`ss`,PULL_EXISTS] >> qexists_tac `x` >> rw[] >>
       `{u0 | u0 IN U /\ x IN u0} <> {}`
         by (`x IN {x | ?s. s IN U /\ x IN s}` by metis_tac[SUBSET_DEF] >>
	    fs[] >> `?t. t IN {u0 | u0 IN U /\ x IN u0}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
	    qexists_tac `s` >> fs[]) >>
       `(CHOICE {u0 | u0 IN U /\ x IN u0}) IN {u0 | u0 IN U /\ x IN u0}` by metis_tac[CHOICE_DEF] >>
       fs[]) >>
  metis_tac[]);
  


val finsat_extension_lemma = store_thm(
  "finsat_extension_lemma",
  ``finsat A μ ν ==> ?B. A ⊆ B /\ finsat B μ ν /\
                     (!C. B ⊆ C /\ finsat C μ ν ==> C = B)``,
  rw[] >>
  qabbrev_tac
  `r = { (s1,s2) | finsat s1 μ ν /\ finsat s2 μ ν /\ A ⊆ s1 /\ s1 ⊆ s2}` >>
  qabbrev_tac `s = { g | finsat g μ ν /\ A ⊆ g }` >>
  `partial_order r s`
  by (simp[Abbr`r`, Abbr`s`, partial_order_def, reflexive_def, transitive_def,
           domain_def, range_def] >> rw[] >> simp[]
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- metis_tac[SUBSET_TRANS]
      >- (simp[antisym_def] >> rw[] >> fs[] >> metis_tac[SUBSET_ANTISYM])) >>
  `s ≠ ∅` by (simp[EXTENSION, Abbr`s`] >> metis_tac[SUBSET_REFL]) >>
  `∀t. chain t r ==> upper_bounds t r ≠ ∅`
    by (rw[] >> Cases_on `t = {}` (* 2 *)
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `A` >>
            simp[range_def] >> qexists_tac `A` >> rw[])
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `BIGUNION t` >> rw[] (* 2 *)
          >- (* BIGUNION is in (range of) relation *)
             (* BIGUNION is proper filter *)
	     (simp[range_def] >> qexists_tac `A` >> rw[] (* 2 *)
	    >- (irule UNION_finsat_finsat (* 2 *)
	      >- (fs[chain_def] >> rw[] >> first_x_assum (qspecl_then [`A'`,`B`] mp_tac) >> rw[] >> metis_tac[])
              >- (fs[chain_def] >> metis_tac[]))
             (* contain f *)
	    >- (fs[chain_def] >> rw[SUBSET_DEF] >>
	      `?a. a IN t` by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `a` >> rw[] >>
	      `A ⊆ a` suffices_by metis_tac[SUBSET_DEF] >>
	      first_x_assum (qspecl_then [`a`,`a`] mp_tac) >> rw[]))
             (* indeed upper bound *)
          >- (`!y. y IN t ==> finsat y μ ν /\ finsat (BIGUNION t) μ ν /\ A SUBSET y /\
                   y SUBSET BIGUNION t` suffices_by metis_tac[] >> rw[] (* 4 *)
            >- (fs[chain_def] >> metis_tac[])
	    >- (irule UNION_finsat_finsat (* 2 *)
	      >- (fs[chain_def] >> rw[] >> first_x_assum (qspecl_then [`A'`,`B`] mp_tac) >> rw[] >> metis_tac[])
              >- (fs[chain_def] >> metis_tac[]))
	    >- (fs[chain_def] >> first_x_assum (qspecl_then [`y`,`y`] mp_tac) >> metis_tac[])
	    >- (rw[SUBSET_DEF,BIGUNION] >> metis_tac[])))) >>
  `?x. x IN maximal_elements s r` by metis_tac[zorns_lemma] >>
  fs[maximal_elements_def,Abbr`r`,Abbr`s`] >> qexists_tac `x` >> rw[] >>
  `A ⊆ C` by (fs[SUBSET_DEF] >> metis_tac[]) >> metis_tac[]);


val FALSE_NOTIN_maximal_finsat = store_thm(
  "FALSE_NOTIN_maximal_finsat",
  ``finsat B μ ν /\ (!C. B SUBSET C /\ finsat C μ ν ==> C = B) ==>
      (!t. (fNOT (fEQ t t)) NOTIN B)``,
  rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> fs[finsat_def,psatisfiable_def] >>
  `{fNOT (fEQ t t)} ⊆ B` by rw[SUBSET_DEF] >>
  `FINITE {fNOT (fEQ t t)}` by rw[] >>
  last_x_assum (qspecl_then [`{fNOT (fEQ t t)}`] mp_tac) >> rw[] >>
  rw[fsatis_def,feval_def]);


val fsatis_fIMP = store_thm(
  "fsatis_fIMP",
  ``!M σ. fsatis M σ (fIMP p q) ==> fsatis M σ p ==> fsatis M σ q``,
  rw[] >> Cases_on `p` >> Cases_on `q` >> fs[fsatis_def,interpret_def,fIMP_def,feval_def] >> qexists_tac `x` >> rw[]);
  


val maximal_finsat_closed_under_fIMP = store_thm(
  "maximal_finsat_closed_under_fIMP",
  ``finsat B μ ν /\ (!C. B SUBSET C /\ finsat C μ ν ==> C = B) ==>
      (!p q. (fIMP p q) IN B <=> (p IN B ==> q IN B))``,
  rw[EQ_IMP_THM] (* 2 *)
  >- fs[finsat_def,psatisfiable_def] >>
     `B ⊆ {q} ∪ B` by rw[SUBSET_DEF] >>
     first_x_assum (qspecl_then [`{q} ∪ B`] mp_tac) >> rw[] >>
     `{q} UNION B = B`
       suffices_by (rw[UNION_DEF,EXTENSION,EQ_IMP_THM]) >>
     first_x_assum irule >> rw[] >> Cases_on `q IN s0` (* 2 *)
     >- `s0 = (s0 DIFF {q}) ∪ {q}`
          by (rw[EXTENSION,EQ_IMP_THM,DIFF_DEF] >> metis_tac[]) >>
	`s0 DIFF {q} ⊆ B`
	  by (rw[SUBSET_DEF,DIFF_DEF] >> fs[SUBSET_DEF] >> metis_tac[]) >>
	rw[] >> `FINITE (s0 DIFF {q})` by metis_tac[FINITE_DIFF] >>
	`?M σ. !f. f IN (s0 DIFF {q}) ==> fsatis M σ f` by metis_tac[] >>
	qexists_tac `M` >> qexists_tac `σ` >> rw[] >> 
	
     >- (`s0 ⊆ B` by (fs[SUBSET_DEF] >> rw[] >> `x <> q` by metis_tac[] >> metis_tac[]) >> metis_tac[])
  >- Cases_on `p IN B` (* 2 *)
     >- `q IN B` by metis_tac[] >>
        `B ⊆ B ∪ {fIMP p q}` by rw[SUBSET_DEF] >>
	`B ∪ {fIMP p q} = B` suffices_by rw[UNION_DEF,EXTENSION,EQ_IMP_THM] >>
	first_x_assum irule (* 2 *) >- rw[]
	>- SPOSE_NOT_THEN ASSUME_TAC >> fs[finsat_def,psatisfiable_def] >>
	   Cases_on `(fIMP p q) IN s0` (* 2 *) (* 2 *)
	   >- Cases_on `p IN s0` >> 




val compactness_theorem = store_thm(
  "compactness_theorem",
  ``!Σ. (!Σ0. FINITE Σ0 /\ Σ0 ⊆ Σ ==> (?M σ. !f. f IN Σ0 ==> fsatis M σ f)) ==>
         ?M σ. (!f. f IN Σ ==> fsatis M σ f)``,




*)

val _ = export_theory();

 
