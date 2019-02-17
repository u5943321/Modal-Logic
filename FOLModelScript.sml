open HolKernel Parse boolLib bossLib;
open FOLSyntaxTheory;


val _ = new_theory "FOLModel";


val models2worlds_def = Define`
  models2worlds MS = \i. (MS i).domain`;

val ultraproduct_model_def = Define`
!U I MS.
      ultraproduct_model U I MS =
      <| domain := ultraproduct_model U I (models2worlds MS);
         consts := \n. 
	 fnsyms := \x y. ARB;
	 predsyms := \p 










frame :=
          <|world := ultraproduct U I (models2worlds MS);
            rel :=
              (\fu gu.
                  ?f g.
                     f IN fu /\ g IN gu /\
                     {i | i IN I /\ (MS i).frame.rel (f i) (g i)} IN
                     U)|>;
        valt :=
          (\p fu.
              ?f.
                 f IN fu /\ {i | i IN I /\ f i IN (MS i).valt p} IN U)|>





val ultrafilter_theorem = store_thm(
"ultrafilter_theorem",
``!f w. proper_filter f w ==> ?U. ultrafilter U w /\ f SUBSET U``,
rpt strip_tac >>
qabbrev_tac
  `r = { (s1,s2) | proper_filter s2 w /\ proper_filter s1 w /\ f SUBSET s1 /\ s1 ⊆ s2}` >>
qabbrev_tac `s = { g | proper_filter g w /\ f ⊆ g }` >>
`partial_order r s`
  by (simp[Abbr`r`, Abbr`s`, partial_order_def, reflexive_def, transitive_def,
           domain_def, range_def] >> rw[] >> simp[]
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- (rw[SUBSET_DEF] >> metis_tac[])
      >- metis_tac[SUBSET_TRANS]
      >- (simp[antisym_def] >> rw[] >> fs[] >> metis_tac[SUBSET_ANTISYM])) >>
`s ≠ ∅` by (simp[EXTENSION, Abbr`s`] >> metis_tac[SUBSET_REFL]) >>
`∀t. chain t r ==> upper_bounds t r ≠ ∅`
  by (rw[] >> Cases_on `t = {}`
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `f` >>
            simp[range_def] >> qexists_tac `f` >> rw[])
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `BIGUNION t` >> rw[]
          >- (* BIGUNION is in (range of) relation *)
             (* BIGUNION is proper filter *)
	     (simp[range_def] >> qexists_tac `f` >> rw[]
	     (* is proper filter *)
	    >- (irule UNION_proper_proper
	      >- (fs[chain_def] >> metis_tac[])
	      >- (fs[chain_def] >> metis_tac[])
	      >- metis_tac[proper_filter_def,filter_def]
	      >- rw[])
             (* contain f *)
	    >- (fs[chain_def,Abbr`s`] >> rw[SUBSET_DEF] >>
	      `?a. a IN t` by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `a` >> rw[] >> metis_tac[SUBSET_DEF]))
             (* indeed upper bound *)
          >- (`y IN t ==> proper_filter (BIGUNION t) w ∧ proper_filter y w ∧ f ⊆ y ∧ y ⊆ BIGUNION t` suffices_by metis_tac[] >> rw[]
	    >- (irule UNION_proper_proper >> rw[]
	        >- (fs[chain_def] >> metis_tac[])
	        >- (fs[chain_def] >> metis_tac[])
	        >- metis_tac[proper_filter_def,filter_def])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (rw[SUBSET_DEF,BIGUNION] >> metis_tac[])))) >>
 `?x. x IN maximal_elements s r` by metis_tac[zorns_lemma] >>
 fs[maximal_elements_def,Abbr`r`,Abbr`s`] >> qexists_tac `x` >> rw[] >>
 irule maximal_ultrafilter >> rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
 `proper_filter S' w` by metis_tac[proper_filter_def] >>
 `x <> S'` by metis_tac[PSUBSET_DEF] >>
 `x = S'` by (first_x_assum irule >> fs[] (* 2 *)
 >> metis_tac[PSUBSET_DEF,SUBSET_TRANS]));


val fvars_def = Define`
  fvars (fRrel a t1 t2) = tvars t1 ∪ tvars t2 /\
  fvars (fPrel a t) = tvars t /\
  fvars (fDISJ ff1 ff2) = (fvars ff1) ∪ (fvars ff2) /\
  fvars (fNOT ff) = fvars ff /\
  fvars (fEXISTS n ff) = n INSERT (fvars ff) /\
  fvars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;

val qfree_def = Define`
    (qfree (fRrel a t1 t2) = T) /\
    (qfree (fPrel a t) = T) /\
    (qfree (fDISJ ff1 ff2) = (qfree ff1 /\ qfree ff2)) /\
    (qfree (fNOT ff) = qfree ff) /\
    (qfree (fEXISTS n ff) = F) /\
    (qfree (fEQ t1 t2) = T)`;


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
    by (rw[] >> Cases_on `t = {}`
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `A` >>
            simp[range_def] >> qexists_tac `A` >> rw[])
        >- (simp[chain_def, upper_bounds_def, Abbr`r`] >> rw[] >>
            simp[Once EXTENSION] >>
            qexists_tac `BIGUNION t` >> rw[]
          >- (* BIGUNION is in (range of) relation *)
             (* BIGUNION is proper filter *)
	     (simp[range_def] >> qexists_tac `A` >> rw[]
	     (* is proper filter *)
	    >- (irule UNION_proper_proper
	      >- (fs[chain_def] >> metis_tac[])
	      >- (fs[chain_def] >> metis_tac[])
	      >- metis_tac[proper_filter_def,filter_def]
	      >- rw[])
             (* contain f *)
	    >- (fs[chain_def,Abbr`s`] >> rw[SUBSET_DEF] >>
	      `?a. a IN t` by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `a` >> rw[] >>
	      `A ⊆ a` suffices_by metis_tac[SUBSET_DEF] >>
	      `a IN t /\ a IN t` suffices_by metis_tac[] last_x_assum imp_res_tac
	      first_x_assum irule
	      `(finsat a μ ν /\ finsat a μ ν /\ A SUBSET a /\ a SUBSET a) \/
	      (finsat a μ ν /\ finsat a μ ν /\ A SUBSET a /\ a SUBSET a)` by metis_tac[]))
             (* indeed upper bound *)
          >- (`y IN t ==> proper_filter (BIGUNION t) w ∧ proper_filter y w ∧ f ⊆ y ∧ y ⊆ BIGUNION t` suffices_by metis_tac[] >> rw[]
	    >- (irule UNION_proper_proper >> rw[]
	        >- (fs[chain_def] >> metis_tac[])
	        >- (fs[chain_def] >> metis_tac[])
	        >- metis_tac[proper_filter_def,filter_def])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (fs[chain_def] >> metis_tac[])
	    >- (rw[SUBSET_DEF,BIGUNION] >> metis_tac[])))) >>
  








val thm_A_19 = store_thm(
  "thm_A_19",
  ``!ff. fsatis <=> fsati








val _ = export_theory();

