open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOLcompactness";


val _ = Datatype`
        fterm = fVar num
	       | fConsts num (fterm list) ;
	fform = fFALSE
	       |fRrel 'p fterm fterm
	       | fPrel 'p fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       `; 

val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;

val fIMP_def = Define`
  fIMP ff1 ff2 = fDISJ (fNOT ff1) ff2`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

val tvars_def = tDefine "tvars" `
  tvars (fVar a) = {a} /\
  tvars (fConsts a ts) = BIGUNION (set (MAP tvars ts))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` >>
     simp[definition "fterm_size_def"] >> rpt strip_tac >> rw[] >>
     fs[])

val tfns_def = tDefine "tfns" `
  tfns (fVar a) = {} /\
  (tfns (fConsts a ts) = (a, LENGTH ts) INSERT (BIGUNION (set (MAP tfns ts))))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffns_def = Define`
  ffns fFALSE = {} /\
  ffns (fRrel a ft1 ft2) = (tfns ft1) ∪ (tfns ft2) /\ 
  ffns (fPrel a ft) = tfns ft /\
  ffns (fDISJ ff1 ff2) = (ffns ff1) ∪ (ffns ff2) /\
  ffns (fNOT ff) = ffns ff /\
  ffns (fEXISTS n ff) = ffns ff`;

val fprs_def = Define`
  fprs fFALSE = {} /\
  fprs (fRrel a ft1 ft2) = {(a,2)} /\
  fprs (fPrel a ft) ={(a,1)} /\
  fprs (fDISJ ff1 ff2) = (fprs ff1) ∪ (fprs ff2) /\
  fprs (fNOT ff) = fprs ff /\
  fprs (fEXISTS n ff) = fprs ff`;

val fns_def = Define`
  fns fms = BIGUNION {ffns f| f IN fms}`;

val prs_def = Define`
  prs fms = BIGUNION {fprs f| f IN fms}`;

val language_def = Define`
  language fms = (fns fms, prs fms)`;

val tfvs_def = tDefine "tfvs" `
  tfvs (fVar x) = {x} /\
  tfvs (fConsts a ts) = BIGUNION (set (MAP tfvs ts))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffvs_def = Define`
  ffvs fFALSE = {} /\
  ffvs (fRrel a ft1 ft2) = (tfvs ft1) ∪ (tfvs ft2) /\
  ffvs (fPrel a ft) = tfvs ft /\
  ffvs (fDISJ ff1 ff2) = (ffvs ff1) ∪ (ffvs ff2) /\
  ffvs (fNOT ff) = ffvs ff /\
  ffvs (fEXISTS n ff) = (ffvs ff) DELETE n`

val tsubst_def = tDefine "tsubst" `
  tsubst v (fVar x) = v x /\
  tsubst v (fConsts a ts) = fConsts a (MAP (tsubst v) ts)
  ` (WF_REL_TAC `measure (fterm_size o SND)` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val VARIANT_def = Define`
  VARIANT vs = (MAX_SET vs) + 1`;


val fsubst_def = Define`
  fsubst v fFALSE = fFALSE /\
  fsubst v (fRrel a ft1 ft2) = fRrel a (tsubst v ft1) (tsubst v ft2) /\
  fsubst v (fPrel a ft) = fPrel a (tsubst v ft) /\
  fsubst v (fDISJ ff1 ff2) = fDISJ (fsubst v ff1) (fsubst v ff2) /\
  fsubst v (fNOT ff) = fNOT (fsubst v ff) /\
  fsubst v (fEXISTS n ff) = if (?y. y IN (ffvs (fEXISTS n ff)) /\ n IN tfvs ((n =+ fVar n) v y))
                               then (fEXISTS (VARIANT (ffvs (fsubst ((n =+ fVar n) v) ff))) (fsubst ((n =+ fVar n) v) ff))
			    else (fEXISTS n (fsubst ((n =+ fVar n) v) ff))`



----------------------------------------------------

val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              fnsyms : num -> 'a list -> 'a;
		      predsyms : 'p -> 'a -> bool;
		      relsyms : 'r -> 'a -> 'a -> bool;
		      |>`;

val teval_def = tDefine "teval" `
  teval M v (fVar x) = v x /\
  teval M v (fConsts f l) = M.fnsyms f (MAP (teval M v) l)
  ` (WF_REL_TAC `measure (fterm_size o (\(a,b,c).c))` >> rpt gen_tac >> Induct_on `l` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val feval_def = Define`
  feval M v fFALSE = F /\
  feval M v (fRrel a ft1 ft2) = M.relsyms a (teval M v ft1) (teval M v ft2) /\
  feval M v (fPrel a ft) = M.predsyms a (teval M v ft) /\
  (feval M v (fDISJ ff1 ff2) = (feval M v ff1 \/ feval M v ff2)) /\
  feval M v (fNOT ff) = ¬(feval M v ff) /\
  feval M v (fEXISTS n ff) = ?x. x IN M.domain /\ feval M ((n =+ x) v) ff`;

val valuation_def = Define`
  valuation M v = (!x. v x IN M.domain)`;

val fsatis_def = Define`
  fsatis M v ff = (valuation M v /\ feval M v ff)`;
 
val satisfies_fset_def = Define`
  satisfies_fset M fms = (!v p. valuation M v /\ p IN fms ==> fsatis M v p)`;

val qfree_def = Define`
    (qfree fFALSE = T) /\
    (qfree (fRrel a t1 t2) = T) /\
    (qfree (fPrel a t) = T) /\
    (qfree (fDISJ ff1 ff2) = (qfree ff1 /\ qfree ff2)) /\
    (qfree (fNOT ff) = qfree ff) /\
    (qfree (fEXISTS n ff) = F)`;

val (prenex_rules, prenex_ind, prenex_cases) = Hol_reln`
  (!ff. qfree ff ==> prenex ff) /\
  (!ff n. prenex ff ==> prenex (fEXISTS n ff)) /\
  (!ff n. prenex ff ==> prenex (fFORALL n ff))`

val (universal_rules, universal_ind, universal_cases) = Hol_reln`
  (!ff. qfree ff ==> universal ff) /\
  (!ff n. prenex ff ==> universal (fFORALL n ff))`

val size_def = Define`
  size fFALSE = 1 /\
  size (fRrel a t1 t2) = 1 /\
  size (fPrel a f) = 1 /\
  size (fDISJ ff1 ff2) = size ff1 + size ff2 + 1 /\
  size (fNOT ff) = size ff + 1 /\
  size (fEXISTS n ff) = size ff + 2`
  
val size_fsubst = store_thm(
  "size_fsubst",
  ``!p i. size p = size (fsubst i p)``,
   Induct_on `p` >> rw[] (* 6 *)
   >- rw[fsubst_def]
   >- (rw[fsubst_def] >> Cases_on `f` >> Cases_on `f0` >> fs[tsubst_def,size_def]) (* 4 *)
   >- (rw[fsubst_def] >> Cases_on `f` >> fs[tsubst_def,size_def])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def] >> metis_tac[])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def])
   >- (rw[fsubst_def] >> fs[tsubst_def,size_def]));
           
val Prenex_right_def = tDefine "Prenex_right" `
  Prenex_right p fFALSE = fDISJ p fFALSE /\
  Prenex_right p (fRrel a t1 t2) = fDISJ p (fRrel a t1 t2) /\
  Prenex_right p (fPrel a t) = fDISJ p (fPrel a t) /\
  Prenex_right p (fDISJ ff1 ff2) = fDISJ p (fDISJ ff1 ff2) /\
  (Prenex_right p (fNOT ff) = case ff of
                                    fEXISTS n (fNOT ff0) => 
                                      let y = VARIANT ((ffvs ff) ∪ (ffvs p)) in
			              fFORALL y
			                (Prenex_right p (fsubst ((n =+ fVar y) fVar) ff0))
			           | _ => (fDISJ p (fNOT ff))) /\
  Prenex_right p (fEXISTS n q) = fEXISTS (VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))))
                                        (Prenex_right p (fsubst ((n =+ fVar (VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))))) fVar) q))
  ` (WF_REL_TAC `measure (size o SND)` >> rw[] (* 2 *)
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n (fNOT ff0)) ∪ ffvs p))) fVar) ff0) = size ff0`
          by metis_tac[size_fsubst] >>
	`size ff0 < size (fNOT (fEXISTS n (fNOT ff0)))` suffices_by metis_tac[] >> rw[size_def])
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))) fVar) q) = size q`
          by metis_tac[size_fsubst] >>
`size q < size (fEXISTS n q)` suffices_by metis_tac[] >> rw[size_def]))



val Prenex_right_qfree = store_thm(
  "Prenex_right_qfree",
  ``!ff. qfree ff ==> !ff'. Prenex_right ff' ff = fDISJ ff' ff``,
  Cases_on `ff` >> rw[qfree_def,Prenex_right_def] >> Cases_on `f` >> fs[qfree_def]);
  

val Prenex_left_def = tDefine "Prenex_left" `
  Prenex_left fFALSE p = Prenex_right fFALSE p /\
  Prenex_left (fRrel a t1 t2) p = Prenex_right (fRrel a t1 t2) p /\
  Prenex_left (fPrel a t) p = Prenex_right (fPrel a t) p /\
  Prenex_left (fDISJ ff1 ff2) p = fDISJ (fDISJ ff1 ff2) p /\
  (Prenex_left (fNOT ff) p = case ff of
                                    fEXISTS n (fNOT ff0) => 
                                      let y = VARIANT ((ffvs ff) ∪ (ffvs p)) in
			              fFORALL y
			                (Prenex_left (fsubst ((n =+ fVar y) fVar) ff0) p)
			           | _ => (fDISJ (fNOT ff) p)) /\
  Prenex_left (fEXISTS n q) p = let y = VARIANT (ffvs (fEXISTS n q) ∪ (ffvs p)) in
                                  fEXISTS y
                                        (Prenex_left (fsubst ((n =+ fVar y) fVar) q) p)
  ` (WF_REL_TAC `measure (size o FST)` >> rw[] (* 2 *)
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n (fNOT ff0)) ∪ ffvs p))) fVar) ff0) = size ff0`
          by metis_tac[size_fsubst] >>
	`size ff0 < size (fNOT (fEXISTS n (fNOT ff0)))` suffices_by metis_tac[] >> rw[size_def])
     >- (`size (fsubst ((n =+ fVar (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))) fVar) q) = size q`
          by metis_tac[size_fsubst] >>
         `size q < size (fEXISTS n q)` suffices_by metis_tac[] >> rw[size_def]))



val pushnot_def = Define`
  (pushnot (fNOT ff) = case ff of
                           | fEXISTS n (fNOT ff0) => fEXISTS n (pushnot ff0)
			   | x => x) /\
  pushnot (fEXISTS n ff) = fFORALL n (pushnot ff) /\
  pushnot x = fNOT x`;
  
val _ = export_rewrites ["pushnot_def"]

val pushnot_qfree_qfree = store_thm(
  "pushnot_qfree_qfree",
  ``!ff. qfree ff ==> qfree (pushnot ff)``,
  Induct_on `ff` >> rw[qfree_def] >> fs[] >> Cases_on `ff` >> fs[qfree_def]);

val pushnot_fFORALL = store_thm(
  "pushnot_fFORALL[simp]",
  ``pushnot (fFORALL n p) = fEXISTS n (pushnot p)``,
  rw[fFORALL_def]);

val fEXISTS_NEQ_fFORALL = store_thm(
  "fEXISTS_NEQ_fFORALL[simp]",
  ``fEXISTS n f <> fFORALL m g``,
  rw[fFORALL_def]);

val pushnot_prenex_prenex = store_thm(
  "pushnot_prenex_prenex",
  ``!f. prenex f ==> prenex (pushnot f)``,
  Induct_on `prenex` >> rw[pushnot_def] (* 3 *)
  >> metis_tac[prenex_rules,pushnot_qfree_qfree]);

val Prenex_def = Define`
  Prenex fFALSE = fFALSE /\
  Prenex (fRrel a t1 t2) = (fRrel a t1 t2) /\
  Prenex (fPrel a t) = (fPrel a t) /\
  Prenex (fDISJ ff1 ff2) = Prenex_left (Prenex ff1) (Prenex ff2) /\
  (Prenex (fNOT ff) = case Prenex ff of
                        | fNOT ff0 => ff0
                        | fEXISTS n ff0 => fFORALL n (pushnot ff0)
			| x => fNOT x) /\
  Prenex (fEXISTS n ff) = fEXISTS n (Prenex ff)`




val prenex_Prenex_left = store_thm(
  "prenex_Prenex_left",
  ``!ff. prenex ff ==> !ff'. prenex ff' ==> prenex (Prenex_left ff ff')``,
  Induct_on `prenex ff` >> strip_tac (* 2 *)
	    >- strip_tac >> strip_tac >> Induct_on `prenex ff'` >> rw[] (* 3 *)
	       >-  cheat
	    
  val prenex_fNOT_prenex = store_thm(
	  "prenex_fNOT_prenex",
``!ff. prenex ff ==> !ff0. ff = fNOT ff0 ==> prenex ff0``,
Induct_on `prenex` >>

	  >- fs[fFORALL_def] >> rw[] >> 

     
val prenex_Prenex = store_thm(
  "prenex_Prenex",
  ``!ff. prenex (Prenex ff)``,
  Induct_on `ff` >> rw[Prenex_def,Prenex_left_def,Prenex_right_def,qfree_def,prenex_rules] (* 2 *)
  >- fs[Once prenex_cases] (* 2 *)
     >- rw[qfree_def] >>
     


     Cases_on `Prenex ff` >> rw[] (* 6 *) 
     >- (`qfree (fNOT fFALSE)` by fs[qfree_def] >> metis_tac[prenex_rules])
     >- (`qfree (fNOT (fRrel p f f0))` by fs[qfree_def] >> metis_tac[prenex_rules])
     >- (`qfree (fNOT (fPrel p f))` by fs[qfree_def] >> metis_tac[prenex_rules])
     >- 

-------------------------------------------------------------
 
val Skolem1_def = Define`
  Skolem1 f x p =
    fsubst ((x =+ (fConsts f (MAP fVar (SET_TO_LIST (ffvs (fEXISTS x p)))))) fVar) p`



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




val TFVL_def = Define`
TFVL (fVar a) = [a] /\
TFVL (fConst a) = []`;




val prenex_right_def = Define`
  


val compactness_theorem = store_thm(
  "compactness_theorem",
  ``!Σ. (!Σ0. FINITE Σ0 /\ Σ0 ⊆ Σ ==> (?M σ. !f. f IN Σ0 ==> fsatis M σ f)) ==>
         ?M σ. (!f. f IN Σ ==> fsatis M σ f)``,

val _ = export_theory();

 
