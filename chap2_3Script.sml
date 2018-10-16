open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

open chap2_1Theory;
open chap2_2Theory;
open IBCDNFTheory;
open equiv_on_partitionTheory;


(* open chap2_3Theory; *)

val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_3";

(* finite model property via selection *)


(* prop 2.29 *)

val DEG_def =
  Define
    `DEG (VAR p) = 0 /\
     DEG (FALSE) = 0 /\
     DEG (NOT form) = DEG form /\
     DEG (DISJ form1 form2) = MAX (DEG form1) (DEG form2) /\
     DEG (DIAM form) = (DEG form) + 1`;

(* base case *)
val FUNSPACE_def = Define`
FUNSPACE s t = {f| (!x. x IN s ==> (f x) IN t) /\ (!x. x NOTIN s ==> (f x) = ARB)}`;

val FUNSPACE_INJ_POW_CROSS = store_thm(
"FUNSPACE_INJ_POW_CROSS",
``INJ (λf. {(x, (f x))| x IN s}) (FUNSPACE s t) (POW (s CROSS t))``,
rw[INJ_DEF,FUNSPACE_def]
>- (simp[IN_POW,SUBSET_DEF,PULL_EXISTS])
>- (rw[FUN_EQ_THM] >> fs[EXTENSION] >> metis_tac[pairTheory.PAIR_EQ]));

val FINITE_FUNSPACE = store_thm(
"FINITE_FUNSPACE",
``!s t. FINITE s /\ FINITE t ==> FINITE (FUNSPACE s t)``,
metis_tac[FINITE_POW,FINITE_CROSS,FINITE_INJ,FUNSPACE_INJ_POW_CROSS]);

val univ_FUNSPACE = store_thm(
"univ_FUNSPACE",
``univ (:'a -> 'b) = FUNSPACE (univ (:'a)) (univ (:'b))``,
rw[FUNSPACE_def,EXTENSION]);

val peval_satis = store_thm(
"peval_satis",
``!M w f. propform f /\ w IN M.frame.world ==> (satis M w f <=> peval (λa. w IN M.valt a) f)``,
Induct_on `f` >> rw[] 
>> metis_tac[satis_def]);


val equiv_peval = store_thm(
"equiv_peval",
``!f1 f2. propform f1 /\ propform f2 /\ (!σ. peval σ f1 = peval σ f2) ==> (!M w. satis M w f1 <=> satis M w f2)``,
rw[] >> eq_tac >> rw[] >>
`w IN M.frame.world` by metis_tac[satis_in_world]
>> metis_tac[peval_satis,satis_in_world]);

val peval_equiv = store_thm(
"peval_equiv",
``!f1 f2. propform f1 /\ propform f2 /\ (!M w. satis M w f1 <=> satis M w f2) ==> (!σ. peval σ f1 = peval σ f2)``,
gen_tac >> gen_tac >> strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
`?σ. (peval σ f1 /\ ¬(peval σ f2)) \/ (¬(peval σ f1) /\ peval σ f2)` by metis_tac[] 
>- (`?M w. satis M w f1 /\ ¬satis M w f2` suffices_by metis_tac[] >>
   qexists_tac `<| frame := <| world := {1};
                           rel := λn1 n2. (n1 = 1 /\ n2 = 1) |>;
                   valt := λa w. (σ a) |>` >>
   qabbrev_tac `M = <| frame := <| world := {1};
                           rel := λn1 n2. (n1 = 1 /\ n2 = 1) |>;
                   valt := λa w. (σ a) |>` >>
   qexists_tac `1` >> rw[]
   >- (`satis M 1 f1` suffices_by metis_tac[] >>
      `1 IN M.frame.world` by fs[Abbr`M`] >>
      `peval (λa. 1 ∈ M.valt a) f1` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])
   >- (`1 IN M.frame.world` by fs[Abbr`M`] >>
      `¬(peval (λa. 1 ∈ M.valt a) f2)` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[]))
>- (`?M w. ¬satis M w f1 /\ satis M w f2` suffices_by metis_tac[] >>
   qexists_tac `<| frame := <| world := {1};
                           rel := λn1 n2. (n1 = 1 /\ n2 = 1) |>;
                   valt := λa w. (σ a) |>` >>
   qabbrev_tac `M = <| frame := <| world := {1};
                           rel := λn1 n2. (n1 = 1 /\ n2 = 1) |>;
                   valt := λa w. (σ a) |>` >>
   qexists_tac `1` >> rw[]
   >- (`¬satis M 1 f1` suffices_by metis_tac[] >>
      `1 IN M.frame.world` by fs[Abbr`M`] >>
      `¬peval (λa. 1 ∈ M.valt a) f1` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])
   >- (`1 IN M.frame.world` by fs[Abbr`M`] >>
      `(peval (λa. 1 ∈ M.valt a) f2)` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])));

val partition_to_peval_well_defined = store_thm(
"partition_to_peval_well_defined",
``!f1 f2. (propform f1 /\ propform f2 /\ equiv f1 f2) ==> ((λf s. peval s f) f1) = ((λf s. peval s f) f2)``,
rw[equiv_def] >> simp[FUN_EQ_THM] >> metis_tac[peval_equiv]);

val IMAGE_peval_singlton = store_thm(
"IMAGE_peval_singlton",
``!x form. x IN (partition equiv {f | propform f}) /\ form IN x ==>
IMAGE (λf s. peval s f) x = {λs. (peval s form)}``,
rw[partition_def] >> rw[IMAGE_DEF] >>
`!f. propform f /\ (equiv x' f) ==> ((λs. peval s f) = (λs. peval s form))` by
(rw[] >> fs[] >> `equiv f form` by metis_tac[equiv_def] >> simp[FUN_EQ_THM] >> metis_tac[partition_to_peval_well_defined]) >>
simp[Once EXTENSION] >> rw[] >> eq_tac >> rw[]
>- metis_tac[]
>- (qexists_tac `form` >> fs[]));

val INJ_peval_partition = store_thm(
"INJ_peval_partition",
``INJ (IMAGE (λf s. peval s f)) (partition equiv {f| propform f}) (univ (:(('a -> bool) -> bool) -> bool))``,
rw[INJ_DEF,UNIV_FUN_TO_BOOL] >> fs[partition_def] >> simp[EXTENSION] >> 
`x IN (partition equiv {f | propform f})` by
(rw[partition_def] >> qexists_tac `x'` >> fs[]) >>
`y IN (partition equiv {f | propform f})` by
(rw[partition_def] >> qexists_tac `x''` >> fs[]) >>
`equiv x' x'` by metis_tac[equiv_def] >> `x' IN x` by simp[] >>
`equiv x'' x''` by metis_tac[equiv_def] >> `x'' IN y` by simp[] >>
`IMAGE (λf s. peval s f) x = {λs. (peval s x')}` by metis_tac[IMAGE_peval_singlton] >>
`IMAGE (λf s. peval s f) y = {λs. (peval s x'')}` by metis_tac[IMAGE_peval_singlton] >> fs[] >>
`∀s. peval s x' ⇔ peval s x''` by fs[FUN_EQ_THM] >>
`equiv x' x''` by metis_tac[equiv_peval,equiv_def] >>
metis_tac[equiv_def]);

val FINITE_equiv_partition = store_thm(
"FINITE_equiv_partition",
``FINITE univ (:'a) ==> FINITE (partition equiv {(f :'a form) | propform f})``,
rw[] >>
`FINITE (univ (:(('a -> bool) -> bool) -> bool))` by (rw[UNIV_FUN_TO_BOOL] >> metis_tac[FINITE_POW]) >> metis_tac[FINITE_INJ,INJ_peval_partition]);


val DEG_0_propform = store_thm(
"DEG_0_propform",
``!f. DEG f = 0 <=> propform f``,
Induct_on `f` >> fs[DEG_def,propform_def]);

val DEG_IBC = store_thm(
"DEG_IBC",
``!phi. DEG phi <= n + 1 <=> IBC phi ({VAR v | T} UNION {DIAM psi | DEG psi <= n})``,
Induct_on `phi` >> rw[DEG_def]
>- (irule (last (CONJUNCTS IBC_rules)) >> simp[])
>- simp[SimpRHS,Once IBC_cases]
>- simp[IBC_rules]
>- simp[SimpRHS,Once IBC_cases]
>- simp[SimpRHS,Once IBC_cases]);


val IBC_EMPTY_lemma = prove(
  ``∀f s. IBC f s ==> s = {} ==> equiv f TRUE \/ equiv f FALSE``,
  Induct_on `IBC` >> rw[] >> fs[equiv_def,satis_def,TRUE_def]);



val equiv_equiv_on_form = store_thm(
"equiv_equiv_on_form",
``!s. equiv equiv_on s``,
rw[equiv_on_def] >> 
metis_tac[equiv_def]);

val FINITE_DNF = store_thm(
    "FINITE_DNF",
    ``!fs. FINITE fs ==> FINITE {f | DNF_OF f fs}``,
    rw[DNF_OF_def,DISJ_OF_def] >>
    `FINITE {c | CONJ_OF c fs}` by metis_tac[FINITE_CONJ_OF] >>
    `FINITE  {f | DISJ_OF0 f {c | CONJ_OF c fs}}` by metis_tac[FINITE_DISJ_OF0] >>
    `FINITE (FALSE INSERT {f | DISJ_OF0 f {c | CONJ_OF c fs}})` by metis_tac[FINITE_INSERT] >>
    `{f | f = ⊥ ∨ DISJ_OF0 f {c | CONJ_OF c fs}} = (FALSE INSERT {f | DISJ_OF0 f {c | CONJ_OF c fs}})` by
    simp[EXTENSION,INSERT_DEF] >> fs[]);
    

val IBC_FINITE = store_thm(
  "IBC_FINITE",
  ``!fs. FINITE fs ==> FINITE (partition equiv {f | IBC f fs})``,
  rw[] >> Cases_on `fs = {}`
  >- (fs[partition_def] >>
     `{t | ∃x. IBC x ∅ ∧ t = {y | IBC y ∅ ∧ equiv x y}} = {{y | IBC y ∅ ∧ equiv TRUE y};{y | IBC y ∅ ∧ equiv FALSE y}}` by (fs[EXTENSION] >> rw[] >> eq_tac >> rw[]
     >- (`equiv x' TRUE \/ equiv x' FALSE` by metis_tac[IBC_EMPTY_lemma]
        >> fs[equiv_def,satis_def,TRUE_def])
     >- (qexists_tac `TRUE` >> rw[] >> rw[Once IBC_cases,TRUE_def] >> metis_tac[IBC_cases])
     >- (qexists_tac `FALSE` >> rw[] >> rw[Once IBC_cases,TRUE_def])) >>
     fs[]) >>
  qabbrev_tac `ff = \s.{d | DNF_OF d fs /\ (!f. f IN s ==> equiv d f)}` >>
  `FINITE {f | DNF_OF f fs}` by metis_tac[FINITE_DNF] >>
  `INJ ff ({f | IBC f fs}//e) (POW {f | DNF_OF f fs})` suffices_by metis_tac[FINITE_POW,FINITE_INJ] >> 
  simp[INJ_DEF,IN_POW] >> rw[]
  >- simp[Abbr`ff`,SUBSET_DEF] >>
  SPOSE_NOT_THEN ASSUME_TAC >>
  `DISJOINT x y` by metis_tac[partition_elements_disjoint,equiv_equiv_on_form]>>
  `(∀f1 f2. f1 ∈ x /\ f2 ∈ x ==> equiv f1 f2) /\
   (∀f1 f2. f1 ∈ y /\ f2 ∈ y ==> equiv f1 f2)`
     by metis_tac [partition_elements_interrelate,equiv_equiv_on_form] >>
  fs[Abbr`ff`] >>
  `equiv equiv_on {f | IBC f fs}` by metis_tac[equiv_equiv_on_form] >>
  `∀f1 f2. f1 ∈ x /\ f2 ∈ y ==> ¬equiv f1 f2` by metis_tac[equiv_on_parition_NOT_R] >>
  qpat_x_assum `GSPEC _ = GSPEC _` mp_tac >> simp[EXTENSION] >>
  `x <> {}` by metis_tac[EMPTY_NOT_IN_partition,equiv_equiv_on_form] >>
  `?fx. fx IN x` by metis_tac[MEMBER_NOT_EMPTY] >>
  `x ⊆ {f | IBC f fs}` by metis_tac[partition_SUBSET] >>
  `IBC fx fs` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  `∃d. DNF_OF d fs /\ equiv fx d` by metis_tac[IBC_DNF_EXISTS] >>
  qexists_tac`d` >> simp[] >>
  `∀f. f ∈ x ==> equiv d f` by metis_tac[equiv_SYM, equiv_TRANS] >> simp[]>>
  `y <> {}` by metis_tac[EMPTY_NOT_IN_partition,equiv_equiv_on_form] >>
  `∃fy. fy ∈ y` by metis_tac[MEMBER_NOT_EMPTY] >>
  qexists_tac `fy` >> simp[] >> metis_tac[equiv_SYM, equiv_TRANS]);


val IBC_partition_equiv = store_thm(
  "IBC_partition_equiv", 
  ``!f fs. IBC f fs ==> fs <> {} ==>
         ?p. IBC p (IMAGE CHOICE (partition equiv fs)) /\ equiv f p``,
Induct_on `IBC` >> rw[]
>- (`∃p. IBC p (IMAGE CHOICE fs//e) ∧ equiv f p /\
   ∃p'. IBC p' (IMAGE CHOICE fs//e) ∧ equiv f' p'` by metis_tac[] >>
   qexists_tac `DISJ p p'` >> rw[]
   >- metis_tac[IBC_cases]
   >- fs[equiv_def,satis_def])
>- (qexists_tac `FALSE` >> rw[Once IBC_cases])
>- (`∃p. IBC p (IMAGE CHOICE fs//e) ∧ equiv f p` by metis_tac[] >>
   qexists_tac `¬p` >> rw[Once IBC_cases] >> fs[equiv_def,satis_def])
>- (fs[partition_def] >>
   qexists_tac `CHOICE {y | y IN fs /\ equiv f y}` >> rw[]
   >- (`(CHOICE {y | y ∈ fs ∧ equiv f y}) IN (IMAGE CHOICE {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv x y}})` by (fs[IMAGE_DEF,PULL_EXISTS] >> qexists_tac `f` >> rw[]) >> metis_tac[IBC_cases]) >>
   `{y | y ∈ fs ∧ equiv f y} <> {}` by (`f IN {y | y ∈ fs ∧ equiv f y}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
   `(CHOICE {y | y ∈ fs ∧ equiv f y}) IN {y | y ∈ fs ∧ equiv f y}` by metis_tac[CHOICE_DEF] >> fs[]));

val IBC_SUBSET = store_thm(
    "IBC_SUBSET",
    ``!f fs. IBC f fs ==> !gs. fs SUBSET gs ==> IBC f gs``,
    Induct_on `IBC` >> rw[]
    >> metis_tac[SUBSET_DEF,IBC_cases]);

      
val FINITE_FINITE_IBC = store_thm(
  "FINITE_FINITE_IBC",
  ``!fs. fs <> {} ==> FINITE (partition equiv fs) ==> FINITE (partition equiv {f | IBC f fs})``,
  rw[] >>
  `FINITE (IMAGE CHOICE fs//e)` by metis_tac[IMAGE_FINITE] >>
  `FINITE {f | IBC f (IMAGE CHOICE fs//e)}//e` by metis_tac[IBC_FINITE] >>
  `fs//e <> {}` by metis_tac[partition_eq_EMPTY] >>
  `?ff. SURJ ff ({f | IBC f (IMAGE CHOICE fs//e)}//e) ({f | IBC f fs}//e)` by
  (fs[partition_def] >> 
  qabbrev_tac `ff = \s. {y | IBC y fs /\ !f. f IN s ==> equiv y f}` >> rw[SURJ_DEF] >>
  qexists_tac `ff` >> rw[]
  >- (fs[partition_def,Abbr`ff`] >> qexists_tac `x'` >> rw[]
     >- (`(IMAGE CHOICE {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv x y}}) SUBSET fs` by
        (rw[IMAGE_DEF,SUBSET_DEF] >>
	`{y | y ∈ fs ∧ equiv x''' y} <> {}` by (`x''' IN {y | y ∈ fs ∧ equiv x''' y}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
	`CHOICE {y | y ∈ fs ∧ equiv x''' y} IN {y | y ∈ fs ∧ equiv x''' y}` by metis_tac[CHOICE_DEF] >>
	fs[]) >>
	metis_tac[IBC_SUBSET])
     >- (rw[EXTENSION,EQ_IMP_THM]
        >- (`{t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv x y}} SUBSET
	    {t |
               ∃x.
                  x ∈ fs ∧
                  ∀x''.
                     (x'' ∈ t ⇒ x'' ∈ fs ∧ equiv x x'') ∧
                     (x'' ∈ fs ∧ equiv x x'' ⇒ x'' ∈ t)}` by (rw[SUBSET_DEF] >> qexists_tac `x'''` >> rw[]) >>
	   qabbrev_tac `A = {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv x y}}` >>
	   qabbrev_tac `B = {t |
                                 ∃x.
                                    x ∈ fs ∧
                                            ∀x''.
                                            (x'' ∈ t ⇒ x'' ∈ fs ∧ equiv x x'') ∧
                                            (x'' ∈ fs ∧ equiv x x'' ⇒ x'' ∈ t)}` >>
	   `(IMAGE CHOICE A) SUBSET (IMAGE CHOICE B)` by metis_tac[IMAGE_SUBSET] >>
	   `IBC x' (IMAGE CHOICE B)` by metis_tac[IBC_SUBSET] >>
	   metis_tac[equiv_REFL,equiv_SYM,equiv_TRANS])
	>> metis_tac[equiv_SYM,equiv_TRANS]))
  >- (fs[partition_def] >>
     qabbrev_tac `A = {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv x y}}` >>
     simp[PULL_EXISTS] >> drule IBC_partition_equiv >> rw[] >> qexists_tac `p` >> rw[]
     >- fs[partition_def,Abbr`A`]
     >- (rw[Abbr`ff`,EXTENSION,EQ_IMP_THM]
        >- (fs[partition_def,Abbr`A`] >> `equiv x p` by fs[] >> metis_tac[equiv_SYM,equiv_TRANS])
	>- metis_tac[equiv_SYM,equiv_TRANS]))) >>
  metis_tac[FINITE_SURJ]);

val NOT_equiv_VAR_DIAM = store_thm(
    "NOT_equiv_VAR_DIAM",
    ``!a f. ¬(equiv (VAR a) (DIAM f))``,
    rw[equiv_def] >>
    `?M w. satis M w (VAR a) /\ ¬(satis M w (◇ f))` suffices_by metis_tac[] >>
    qexists_tac `<| frame := <| world := {1};
                           rel := λn1 n2. F |>;
                   valt := λe w. T|>` >> qexists_tac `1` >> rw[]
    >> rw[satis_def]);




val equiv_add_predecessor = store_thm(
  "equiv_add_predecessor",
  ``!M w f. w IN M.frame.world ==>
            (satis M w f <=>
            satis <| frame := <| world := 0 INSERT {n + 1 | n IN M.frame.world};
                           rel := λn1 n2. ((n1 >= 1 /\ n2 >= 1) /\ (n1 - 1) IN M.frame.world /\ (n2 - 1) IN M.frame.world /\
			   M.frame.rel (n1 - 1) (n2 - 1)) \/ (n1 = 0 /\ n2 = w + 1) |>;
                   valt := λa b. (M.valt a (b - 1)) |> (w + 1) f)``,
  rw[] >> qmatch_abbrev_tac `satis M w f ⇔ satis M' (w + 1) f` >>
  `bounded_mor (\a. a + 1) M M'` by (rw[bounded_mor_def] 
  >- fs[Abbr`M'`]
  >- (fs[Abbr`M'`] >>rw[satis_def] >> fs[IN_DEF])
  >- fs[Abbr`M'`]
  >- (qexists_tac `v' - 1` >> rw[] (* 3 *) >> fs[Abbr`M'`]))
  >> `satis M w f <=> satis M' ((\a. a + 1) w) f` by fs[prop_2_14] >> fs[]);


val equiv_DIAM_lemma = store_thm(
  "equiv_DIAM_lemma",
  ``!f g. ¬(equiv f g) ==> ¬(equiv (DIAM f) (DIAM g))``,
  rw[EQ_equiv_def] >>
  `(satis M w f /\ ¬satis M w g) \/ (¬satis M w f /\ satis M w g)` by metis_tac[]
  >- (qexists_tac `<| frame := <| world := 0 INSERT {n + 1 | n IN M.frame.world};
                           rel := λn1 n2. ((n1 >= 1 /\ n2 >= 1) /\ (n1 - 1) IN M.frame.world /\ (n2 - 1) IN M.frame.world /\
			   M.frame.rel (n1 - 1) (n2 - 1)) \/ (n1 = 0 /\ n2 = w + 1) |>;
                   valt := λa b. (M.valt a (b - 1)) |>` >>
    qmatch_abbrev_tac `?w'. w' IN M'.frame.world /\ (satis M' w' (DIAM f) ⇎ satis M' w' (DIAM g))` >> qexists_tac `0` >> rw[]
    >- fs[Abbr`M'`]
    >- (`satis M' 0 (DIAM f) /\ ¬satis M' 0 (DIAM g)` suffices_by metis_tac[] >> rw[satis_def]
       >- fs[Abbr`M'`]
       >- (qexists_tac `w + 1` >> fs[Abbr`M'`] >> metis_tac[equiv_add_predecessor])
       >- (`!v. M'.frame.rel 0 v /\ v IN M'.frame.world ==> ¬satis M' v g` suffices_by metis_tac[] >> rw[] >>
          fs[Abbr`M'`] (* 2 *) >- fs[] >- metis_tac[equiv_add_predecessor])))
  >> (qexists_tac `<| frame := <| world := 0 INSERT {n + 1 | n IN M.frame.world};
                           rel := λn1 n2. ((n1 >= 1 /\ n2 >= 1) /\ (n1 - 1) IN M.frame.world /\ (n2 - 1) IN M.frame.world /\
			   M.frame.rel (n1 - 1) (n2 - 1)) \/ (n1 = 0 /\ n2 = w + 1) |>;
                   valt := λa b. (M.valt a (b - 1)) |>` >>
    qmatch_abbrev_tac `?w'. w' IN M'.frame.world /\ (satis M' w' (DIAM f) ⇎ satis M' w' (DIAM g))` >> qexists_tac `0` >> rw[]
    >- fs[Abbr`M'`]
    >- (`¬satis M' 0 (DIAM f) /\ satis M' 0 (DIAM g)` suffices_by metis_tac[] >> rw[satis_def]
       >- (`!v. M'.frame.rel 0 v /\ v IN M'.frame.world ==> ¬satis M' v f` suffices_by metis_tac[] >> rw[] >>
          fs[Abbr`M'`] (* 2 *) >- fs[] >- metis_tac[equiv_add_predecessor])
       >- fs[Abbr`M'`]
       >- (qexists_tac `w + 1` >> fs[Abbr`M'`] >> metis_tac[equiv_add_predecessor]))));
  
       
val equiv_DIAM = store_thm(
    "equiv_DIAM",
    ``!f g. equiv (DIAM f) (DIAM g) <=> equiv f g``,
    rw[EQ_IMP_THM]
    >- (SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[equiv_DIAM_lemma])
    >- fs[equiv_def,satis_def]);



val prop_2_29 = store_thm(
"prop_2_29",
``FINITE univ (:'a) ==> !n. FINITE (partition equiv {f:'a form | DEG f <= n})``,
strip_tac >> Induct_on `n` >> simp[]
>- (`FINITE (partition equiv {f:'a form | propform f})` by metis_tac[FINITE_equiv_partition] >>
   `{f: 'a form | DEG f = 0} = {f | propform f}` by (fs[EXTENSION] >> metis_tac[DEG_0_propform]) >> fs[])
>> (* step case *)
   `SUC n = n + 1` by fs[] >> rw[] >>
   `{f | DEG f ≤ n + 1} = {phi | IBC phi ({VAR v | T} UNION {DIAM psi | DEG psi <= n})}` by (fs[EXTENSION] >> metis_tac[DEG_IBC]) >> simp[] >>
   Cases_on `({VAR v | T} ∪ {◇ psi | DEG psi ≤ n}) = {}`
   >- (fs[] >> fs[partition_def] >>
      `{t | ∃x. IBC x ∅ ∧ t = {y | IBC y ∅ ∧ equiv x y}} = {{f | IBC f {} /\ equiv f TRUE};{f | IBC f {} /\ equiv f FALSE}}` by
      (simp[Once EXTENSION] >> rw[] >> eq_tac >> rw[] (* 3 *)
      >- (drule IBC_EMPTY_lemma >> rw[]
         >- (`{y | IBC y ∅ ∧ equiv x' y} = {f | IBC f ∅ ∧ equiv f TRUE}` suffices_by metis_tac[] >>
	    rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv_SYM,equiv_TRANS])
         >- (`{y | IBC y ∅ ∧ equiv x' y} = {f | IBC f ∅ ∧ equiv f FALSE}` suffices_by metis_tac[] >>
	    rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv_SYM,equiv_TRANS]))
      >- (qexists_tac `TRUE` >> rw[]
         >- (rw[Once IBC_cases] >>
	    `∃f. TRUE = ¬f ∧ IBC f ∅` suffices_by metis_tac[] >> qexists_tac `FALSE` >> metis_tac[IBC_cases,TRUE_def])
	 >- (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv_SYM]))
      >- (qexists_tac `FALSE` >> rw[]
         >- rw[Once IBC_cases] 
	 >- (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv_SYM]))) >> fs[])
   >- (irule FINITE_FINITE_IBC (* 2 *)
      >- (`({VAR v | T} ∪ {◇ psi | DEG psi ≤ n})//e = ({VAR v | T}//e) ∪ ({◇ psi | DEG psi ≤ n}//e)` by
         (irule equiv_on_disjoint_parition
	 >- (rw[] >> metis_tac[NOT_equiv_VAR_DIAM])
         >- metis_tac[equiv_equiv_on_form]
	 >- metis_tac[equiv_equiv_on_form]) (* by tactic ends *)
	 >> rw[] (* 2 *)
	    >- (`FINITE {VAR v | T}` suffices_by metis_tac[FINITE_partition] >>
	       `SURJ VAR (𝕌(:α)) {VAR v | T}` suffices_by metis_tac[FINITE_SURJ] >> rw[SURJ_DEF])
	    >- (qabbrev_tac `A = {f | DEG f ≤ n}//e` >> 
	       qabbrev_tac `B = {◇ psi | DEG psi ≤ n}//e` >>
	       `?ff. SURJ ff A B` suffices_by metis_tac[FINITE_SURJ] >>
	       qexists_tac `\s. {DIAM t | t IN s}` >> rw[SURJ_DEF] (* 2 *)
               >- (fs[Abbr`B`] >> rw[Once EXTENSION,partition_def] >> fs[PULL_EXISTS] >> fs[Abbr`A`,partition_def] >>
	          qexists_tac `x` >> rw[] >> eq_tac >> rw[] (* 4 *) >> metis_tac[equiv_DIAM])
	       >- (fs[Abbr`A`,Abbr`B`] (* 2 *)
	          >> (fs[partition_def] >> fs[PULL_EXISTS] >>
		     qexists_tac `psi` >> fs[] >> rw[EXTENSION] >> eq_tac >> rw[] (* 2 *) >> metis_tac[equiv_DIAM]))))
      >- rw[]));


(* n-bisimulation *)


val nbisim_def = Define`
nbisim M M' f n w w' <=>
w IN M.frame.world /\
w' IN M'.frame.world /\
(!m a b. a IN M.frame.world /\ b IN M'.frame.world ==> (m + 1 <= n ==> (f (m + 1)) a b ==> (f m) a b)) /\
((f n) w w') /\
(!v v'. v IN M.frame.world /\ v' IN M'.frame.world ==> ((f 0) v v' ==> !p. satis M v (VAR p) <=> satis M' v' (VAR p))) /\
(!v v' u i. (i + 1 <= n /\ v IN M.frame.world /\ v' IN M'.frame.world /\ u IN M.frame.world /\ M.frame.rel v u /\ (f (i + 1)) v v') ==>
(?u'. u' IN M'.frame.world /\ M'.frame.rel v' u' /\ (f i) u u')) /\
(!v v' u' i. (i + 1 <= n /\ v IN M.frame.world /\ v' IN M'.frame.world /\ u' IN M'.frame.world /\ M'.frame.rel v' u' /\ (f (i + 1)) v v') ==>
(?u. u IN M.frame.world /\ M.frame.rel v u /\ (f i) u u'))`;


val suc_bisim = store_thm(
"suc_bisim",
``!M M' f n w w'. nbisim M M' f (n + 1) w w' ==> nbisim M M' f n w w'``,
rpt strip_tac >>
`w IN M.frame.world` by metis_tac[nbisim_def] >>
`w' IN M'.frame.world` by metis_tac[nbisim_def] >>
`f (n + 1) w w'` by metis_tac[nbisim_def] >>
rw[nbisim_def]
>- (`m + 1 <= n + 1` by simp[] >> metis_tac[nbisim_def])
>- (`n + 1 <= n + 1` by simp[] >> metis_tac[nbisim_def])
>- metis_tac[nbisim_def]
>- (`i + 1 <= n + 1` by simp[] >> fs[nbisim_def] >> metis_tac[])
>- (`i + 1 <= n + 1` by simp[] >> fs[nbisim_def] >> metis_tac[nbisim_def]));

val suc_nbisim_rel = store_thm(
"suc_nbisim_rel",
``!M M' f n w w' v. nbisim M M' f (n + 1) w w' /\ M.frame.rel w v /\ v IN M.frame.world /\ w IN M.frame.world ==>
(?v'. v' IN M'.frame.world /\ M'.frame.rel w' v' /\ nbisim M M' f n v v')``,
rpt strip_tac >> `n + 1 <= n + 1` by simp[] >>
`(f (n + 1)) w w'` by metis_tac[nbisim_def] >>
`w IN M.frame.world` by metis_tac[nbisim_def] >>
`w' IN M'.frame.world` by metis_tac[nbisim_def] >>
fs[nbisim_def] >> `n <= n` by simp[] >>
`∃u'. u' ∈ M'.frame.world ∧ M'.frame.rel w' u' ∧ f n v u'` by metis_tac[] >> qexists_tac`u'` >> rw[]
>> `i <= n` by simp[] >> metis_tac[]);

val suc_nbisim_rel_SYM = store_thm(
"suc_nbisim_rel_SYM",
``!M M' f n w w' v'. nbisim M M' f (n + 1) w w' /\ M'.frame.rel w' v' /\ v' IN M'.frame.world /\ w' IN M'.frame.world ==>
(?v. v IN M.frame.world /\ M.frame.rel w v /\ nbisim M M' f n v v')``,
rpt strip_tac >> `n + 1 <= n + 1` by simp[] >>
`(f (n + 1)) w w'` by metis_tac[nbisim_def] >>
`w IN M.frame.world` by metis_tac[nbisim_def] >>
fs[nbisim_def] >> `n <= n` by simp[] >>
`∃u. u ∈ M.frame.world ∧ M.frame.rel w u ∧ f n u v'` by metis_tac[] >>
qexists_tac`u` >> rw[]
>> `i <= n` by simp[] >> metis_tac[]);


val DIAM_DEG_NOT_ZERO = store_thm(
"DIAM_DEG_NOT_ZERO",
``!phi. DEG (DIAM phi) <> 0``,
rpt strip_tac >> fs[DEG_def]);

val nbisim_rel_trans = store_thm(
"nbisim_rel_trans",
``!M M' f n w w'. nbisim M M' f n w w' ==> (f 0) w w'``,
rpt strip_tac >> Induct_on `n` >> rpt strip_tac
>- metis_tac[nbisim_def]
>- (`SUC n = n + 1` by simp[] >>
   `nbisim M M' f n w w'` by metis_tac[suc_bisim] >>
   metis_tac[]));


val prop_2_31_half1 = store_thm(
"prop_2_31_half1",
``!M M' n w w'. FINITE univ (:'a) ==>(?f. nbisim M M' f n w w') ==> (!(phi: 'a form). DEG phi <= n ==> (satis M w phi <=> satis M' w' phi))``,
gen_tac >> gen_tac >> gen_tac >> Induct_on `n`
>- (rpt strip_tac >>
    `DEG phi = 0` by simp[] >>
    `w IN M.frame.world /\ w' IN M'.frame.world` by metis_tac[nbisim_def] >>
    Induct_on `phi` >> rpt strip_tac 
    >- (`(f 0) w w'` by metis_tac[nbisim_def] >> fs[nbisim_def])
    >- (fs[DEG_def] >> metis_tac[satis_def])
    >- metis_tac[satis_def]
    >- (fs[DEG_def] >> metis_tac[satis_def])
    >- metis_tac[DIAM_DEG_NOT_ZERO])
>- (rw[] >>
    Induct_on `phi` >> simp[DEG_def]
    >- (gen_tac >> first_x_assum irule >> rw[DEG_def] >> metis_tac[suc_bisim,ADD1])
    >- rw[satis_def]
    >- rw[satis_def]
    >- (rw[satis_def] >> metis_tac[nbisim_def]) 
    >- (simp[ADD1, satis_def] >> rw[EQ_IMP_THM] 
      >- metis_tac[nbisim_def]
      >- (`M.frame.rel w v` by fs[IN_DEF] >>
        fs[ADD1] >>
        `?v'. M'.frame.rel w' v' /\ nbisim M M' f n v v' /\ v' ∈ M'.frame.world`
           by metis_tac[ADD1,suc_nbisim_rel] >>
        metis_tac[IN_DEF])
      >- metis_tac[nbisim_def]
      >- (fs[ADD1] >>
       `∃p. p ∈ M.frame.world ∧ M.frame.rel w p ∧ nbisim M M' f n p v` by metis_tac[suc_nbisim_rel_SYM] >>
       metis_tac[]))));


(* ATTEMPTING USE WLOG 

``!Z.
  (!M M' i w w'. Z M M' i w w' ==> Z M' M i w' w) ==>
  ∀M M' n w w'.
     w ∈ M.frame.world ∧ w' ∈ M'.frame.world ∧
     (∀m a b.
         a ∈ M.frame.world ∧ b ∈ M'.frame.world ⇒
         m + 1 ≤ n ⇒
         Z M M' (m + 1) a b ⇒
         Z M M' m a b) ∧ Z M M' n w w' ∧
     (∀v v'.
         v ∈ M.frame.world ∧ v' ∈ M'.frame.world ⇒
         Z M M' 0 v v' ⇒
         ∀p. satis M v (VAR p) ⇔ satis M' v' (VAR p)) ∧
     (∀v v' u i.
         i + 1 ≤ n ∧ v ∈ M.frame.world ∧ v' ∈ M'.frame.world ∧
         u ∈ M.frame.world ∧ M.frame.rel v u ∧ Z M M' (i + 1) v v' ⇒
         ∃u'. u' ∈ M'.frame.world ∧ M'.frame.rel v' u' ∧ Z M M' i u u')
	 ==> nbisim M M' (Z M M') n w w'``,
  rw[nbisim_def] >- metis_tac[] >> `Z M' M (i + 1) v' v` by metis_tac[] >> 


*)





val FINITE_partition_SUBSET = store_thm(
(* SHOULD BE MOVE IN TO partition_equiv *)
  "FINITE_partition_SUBSET",
  ``!R s. R equiv_on s ==> FINITE (partition R s) ==> !a. a ⊆ s ==> FINITE (partition R a)``,
  rw[partition_def] >>
  `?f. INJ f {t | ∃x. x ∈ a ∧ t = {y | y ∈ a ∧ R x y}} {t | ∃x. x ∈ s ∧ t = {y | y ∈ s ∧ R x y}}` suffices_by metis_tac[FINITE_INJ] >>
  qexists_tac `\p. {y | y IN s /\ ?r. r IN p /\ R r y}`	>> rw[INJ_DEF]
  >- (qexists_tac `x` >> rw[]
     >- fs[SUBSET_DEF]
     >- (rw[Once EXTENSION] >> eq_tac >> rw[]
        >- (`x IN s` by metis_tac[SUBSET_DEF] >>
	   `r IN s` by metis_tac[SUBSET_DEF] >>
	   `∀x y z. x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ R x y ∧ R y z ⇒ R x z` by fs[equiv_on_def] >> metis_tac[])
	>- (qexists_tac `x` >> rw[] >>
	   `x IN s` by metis_tac[SUBSET_DEF] >>
	   fs[equiv_on_def])))
  >- (rw[Once EXTENSION] >> eq_tac >> rw[]
     >- (`{y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x y} ∧ R r y} =
         {y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x' y} ∧ R r y} ==> R x' x''` suffices_by metis_tac[] >>
        simp[Once EXTENSION,EQ_IMP_THM] >> rw[] >>
	`x'' IN s` by fs[SUBSET_DEF] >>
	`R x'' x''` by fs[equiv_on_def] >>
	`∃r. (r ∈ a ∧ R x' r) ∧ R r x''` by metis_tac[] >>
	fs[equiv_on_def] >>
	`r IN s` by fs[SUBSET_DEF] >>
	`x' IN s` by fs[SUBSET_DEF] >>
	metis_tac[])
     >- (`{y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x y} ∧ R r y} =
         {y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x' y} ∧ R r y} ==> R x x''` suffices_by metis_tac[] >>
        simp[Once EXTENSION,EQ_IMP_THM] >> rw[] >>
	`x'' IN s` by fs[SUBSET_DEF] >>
	`R x'' x''` by fs[equiv_on_def] >>
	`∃r. (r ∈ a ∧ R x r) ∧ R r x''` by metis_tac[] >>
	fs[equiv_on_def] >>
	`r IN s` by fs[SUBSET_DEF] >>
	`x' IN s` by fs[SUBSET_DEF] >>
	`x IN s` by fs[SUBSET_DEF] >> metis_tac[])));

val CHOICE_BIJ_partition = store_thm(
    "CHOICE_BIJ_partition",
    ``!R s. R equiv_on s ==>
    BIJ CHOICE (partition R s) (IMAGE CHOICE (partition R s))``,
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF] >>
    `x <> {} /\ y <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
    `CHOICE x IN x /\ CHOICE y IN y` by metis_tac[CHOICE_DEF] >>
    `CHOICE x IN y` by fs[] >>
    irule equiv_partition_unique >> map_every qexists_tac [`R`,`s`,`CHOICE x`] >> rw[] >>
    fs[partition_def] >>
    `{y | y ∈ s ∧ R x'' y} <> {}` by (`x'' IN  {y | y ∈ s ∧ R x'' y}` by fs[equiv_on_def] >> metis_tac[MEMBER_NOT_EMPTY]) >>
    `CHOICE {y | y ∈ s ∧ R x'' y} IN {y | y ∈ s ∧ R x'' y}` by metis_tac[CHOICE_DEF] >> fs[]);

val BIGCONJ_EXISTS_DEG = store_thm(
  "BIGCONJ_EXISTS_DEG",
  ``∀s.
     FINITE s ⇒
     (!f. f IN s ==> DEG f <= n) ==>
     ?ff. DEG ff <= n /\
     ∀w M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)``,
  Induct_on `FINITE` >> rw[]
  >- (qexists_tac `TRUE` >> rw[TRUE_def,satis_def,DEG_def])
  >- (`∀f. f ∈ s ⇒ DEG f ≤ n` by metis_tac[] >>
     first_x_assum drule >> rw[] >>
     qexists_tac `AND e ff` >> rw[DEG_def,satis_def,AND_def] >> eq_tac >> rw[]
     >- rw[]
     >> metis_tac[]));



val prop_2_31_half2 = store_thm(
"prop_2_31_half2",
``!M M' n w w'. (FINITE univ (:'a) /\ w IN M.frame.world /\ w' IN M'.frame.world) ==> (!(phi: 'a form). DEG phi <= n ==> (satis M w phi <=> satis M' w' phi)) ==> ?f. nbisim M M' f n w w'``,
rpt strip_tac
>> rw[nbisim_def]
>> qexists_tac `λn n1 n2. (!(phi: 'a form). DEG phi <= n ==> (satis M n1 phi <=> satis M' n2 phi))` >> rw[]
>- metis_tac[DEG_def]
>- (SPOSE_NOT_THEN ASSUME_TAC >>
   `?u'. u' IN M'.frame.world /\ M'.frame.rel v' u'` by 
   (`¬(!u'. u' IN M'.frame.world ==> ¬M'.frame.rel v' u')` suffices_by metis_tac[] >>
   rpt strip_tac >>
   `satis M' v' (BOX FALSE)` by metis_tac[box_vac_true] >>
   `DEG (□ ⊥) = 1` by rw[DEG_def,BOX_def] >>
   `DEG (□ ⊥) <= i + 1` by fs[] >>
   `satis M v (BOX FALSE)` by metis_tac[] >>
   `satis M v (NOT (DIAM TRUE))` by metis_tac[BOX_def,TRUE_def,satis_def] >>
   `¬(satis M v (DIAM TRUE))` by metis_tac[satis_def] >>
   `satis M v (DIAM TRUE)` by metis_tac[diam_exist_true]) >>
   `u' IN {u' | u' ∈ M'.frame.world ∧ M'.frame.rel v' u'}` by simp[] >>
   `∀u'.
          u' ∈ M'.frame.world ⇒ M'.frame.rel v' u' ==>
          ¬(∀form. DEG form <= i ==> (satis M u form ⇔ satis M' u' form))` by metis_tac[] >>
   `∀u'.
          u' ∈ M'.frame.world /\ M'.frame.rel v' u' ==>
          ¬(∀form. DEG form <= i ==> (satis M u form ⇔ satis M' u' form))` by metis_tac[] >>
   `∀u'.
          u' ∈ M'.frame.world /\ M'.frame.rel v' u' ==>
          ¬(∀form. DEG form <= i ==> (¬(¬(satis M u form ⇔ satis M' u' form))))` by metis_tac[] >>
   `∀u'.
          u' ∈ M'.frame.world /\ M'.frame.rel v' u' ==>
          (?form. DEG form <= i /\ ¬(satis M u form ⇔ satis M' u' form))` by metis_tac[] >>
   `∀u'.
          u' ∈ M'.frame.world /\ M'.frame.rel v' u' ==>
          (?form. DEG form <= i /\ satis M u form /\ ¬satis M' u' form)` by
       (rw[] >>
       `∃form. DEG form ≤ i ∧ (satis M u form ⇎ satis M' u'' form)` by metis_tac[] >>
       Cases_on `satis M u form`
       >- (`¬satis M' u'' form` by metis_tac[] >> qexists_tac `form` >> rw[])
       >- (`satis M' u'' form` by metis_tac[] >> qexists_tac `¬form` >> rw[satis_def,DEG_def])) >> 
   qabbrev_tac `s = {f | DEG f <= i /\ ?u'. u' IN M'.frame.world /\ M'.frame.rel v' u' /\ satis M u f /\ ¬satis M' u' f}` >>
   `s ⊆ {f| DEG f <= i}` by (fs[Abbr`s`,SUBSET_DEF]) >>
   `equiv equiv_on {f | DEG f ≤ i}` by metis_tac[equiv_equiv_on_form] >>
   `FINITE s//e` by metis_tac[prop_2_29,FINITE_partition_SUBSET] >>
   `FINITE (IMAGE CHOICE s//e)` by
   (`equiv equiv_on s` by metis_tac[equiv_equiv_on_form] >>
   `BIJ CHOICE s//e (IMAGE CHOICE s//e)` by metis_tac[CHOICE_BIJ_partition] >>
   metis_tac[FINITE_BIJ]) >>
   `equiv equiv_on s` by metis_tac[equiv_equiv_on_form] >> 
   `!p. p IN s//e ==> p <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `!p. p IN s//e ==> (CHOICE p) IN p` by metis_tac[CHOICE_DEF] >>
   `!f. f IN (IMAGE CHOICE s//e) ==> DEG f <= i` by
   (fs[IMAGE_DEF] >> rw[] >> `(CHOICE x) IN x` by metis_tac[] >>
   `x SUBSET s` by fs[partition_def,SUBSET_DEF] >>
   `(CHOICE x) IN s` by metis_tac[SUBSET_DEF] >>
   fs[Abbr`s`]) >>
   `∃ff.
        DEG ff ≤ i ∧
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ (IMAGE CHOICE s//e) ⇒ satis M w f)` by fs[BIGCONJ_EXISTS_DEG] >>
   `∀f. f ∈ IMAGE CHOICE s//e ⇒ satis M u f` by
   (rw[IMAGE_DEF] >>
   `x <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `(CHOICE x) IN x` by metis_tac[CHOICE_DEF] >> fs[partition_def,Abbr`s`] >> rw[] >> fs[]) >>
   `satis M u ff` by metis_tac[] >>
   `satis M v (DIAM ff)` by metis_tac[satis_def] >>
   `DEG (DIAM ff) <= i + 1` by fs[DEG_def] >>
   `¬satis M' v' (DIAM ff)` suffices_by metis_tac[] >> rw[satis_def] >>
   `M'.frame.rel v' v'' /\ v'' IN M'.frame.world ==> ¬satis M' v'' ff` suffices_by metis_tac[satis_def] >>
   simp[PULL_EXISTS] >> rw[] >>
   `∃form. DEG form ≤ i ∧ satis M u form ∧ ¬satis M' v'' form` by metis_tac[] >>
   rw[partition_def,PULL_EXISTS] >>
   `form IN s` by (fs[Abbr`s`] >> qexists_tac `v''` >> rw[]) >>
   qexists_tac `form` >> rw[] >>
   `equiv form form` by metis_tac[equiv_REFL] >> `form IN {y | y ∈ s ∧ equiv form y}` by fs[] >>
   `{y | y ∈ s ∧ equiv form y} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
   `(CHOICE {y | y ∈ s ∧ equiv form y}) IN {y | y ∈ s ∧ equiv form y}` by metis_tac[CHOICE_DEF] >>
   fs[] >> 
   metis_tac[equiv_SYM,equiv_def])
>- (SPOSE_NOT_THEN ASSUME_TAC >>
   `?u. u IN M.frame.world /\ M.frame.rel v u` by 
   (`¬(!u. u IN M.frame.world ==> ¬M.frame.rel v u)` suffices_by metis_tac[] >>
   rpt strip_tac >>
   `satis M v (BOX FALSE)` by metis_tac[box_vac_true] >>
   `satis M v (NOT (DIAM TRUE))` by metis_tac[BOX_def,TRUE_def,satis_def] >>
   `¬(satis M v (DIAM TRUE))` by metis_tac[satis_def] >>
   `satis M' v' (DIAM TRUE)` by metis_tac[diam_exist_true] >>
   `DEG (DIAM TRUE) <= i + 1` by fs[TRUE_def,DEG_def] >>
   metis_tac[]) >>
   `u IN {u | u ∈ M.frame.world ∧ M.frame.rel v u}` by simp[] >>
   `∀u.
          u ∈ M.frame.world ⇒ M.frame.rel v u ==>
          ¬(∀form. DEG form <= i ==> (satis M' u' form ⇔ satis M u form))` by metis_tac[] >>
   `∀u.
          u ∈ M.frame.world /\ M.frame.rel v u ==>
          ¬(∀form. DEG form <= i ==> (satis M' u' form ⇔ satis M u form))` by metis_tac[] >>
   `∀u.
          u ∈ M.frame.world /\ M.frame.rel v u ==>
          ¬(∀form. DEG form <= i ==> (¬(¬(satis M' u' form ⇔ satis M u form))))` by metis_tac[] >>
   `∀u.
          u ∈ M.frame.world /\ M.frame.rel v u ==>
          (?form. DEG form <= i /\ ¬(satis M' u' form ⇔ satis M u form))` by metis_tac[] >>
   `∀u.
          u ∈ M.frame.world /\ M.frame.rel v u ==>
          (?form. DEG form <= i /\ satis M' u' form /\ ¬satis M u form)` by
       (rw[] >>
       last_x_assum drule >> rw[] >> 
       Cases_on `satis M u'' phi`
       >- (`¬satis M' u' phi` by metis_tac[] >> qexists_tac `¬phi` >> rw[satis_def,DEG_def])
       >- (`satis M' u' phi` by metis_tac[] >> qexists_tac `phi` >> rw[])) >> 
   qabbrev_tac `s = {f | DEG f <= i /\ ?u. u IN M.frame.world /\ M.frame.rel v u /\ satis M' u' f /\ ¬satis M u f}` >>
   `s ⊆ {f| DEG f <= i}` by (fs[Abbr`s`,SUBSET_DEF]) >>
   `equiv equiv_on {f | DEG f ≤ i}` by metis_tac[equiv_equiv_on_form] >>
   `FINITE s//e` by metis_tac[prop_2_29,FINITE_partition_SUBSET] >>
   `FINITE (IMAGE CHOICE s//e)` by
   (`equiv equiv_on s` by metis_tac[equiv_equiv_on_form] >>
   `BIJ CHOICE s//e (IMAGE CHOICE s//e)` by metis_tac[CHOICE_BIJ_partition] >>
   metis_tac[FINITE_BIJ]) >>
   `equiv equiv_on s` by metis_tac[equiv_equiv_on_form] >> 
   `!p. p IN s//e ==> p <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `!p. p IN s//e ==> (CHOICE p) IN p` by metis_tac[CHOICE_DEF] >>
   `!f. f IN (IMAGE CHOICE s//e) ==> DEG f <= i` by
   (fs[IMAGE_DEF] >> rw[] >> `(CHOICE x) IN x` by metis_tac[] >>
   `x SUBSET s` by fs[partition_def,SUBSET_DEF] >>
   `(CHOICE x) IN s` by metis_tac[SUBSET_DEF] >>
   fs[Abbr`s`]) >>
   `∃ff.
        DEG ff ≤ i ∧
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ (IMAGE CHOICE s//e) ⇒ satis M w f)` by fs[BIGCONJ_EXISTS_DEG] >>
   `∀f. f ∈ IMAGE CHOICE s//e ⇒ satis M' u' f` by
   (rw[IMAGE_DEF] >>
   `x <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `(CHOICE x) IN x` by metis_tac[CHOICE_DEF] >> fs[partition_def,Abbr`s`] >> rw[] >> fs[]) >>
   `satis M' u' ff` by metis_tac[] >>
   `satis M' v' (DIAM ff)` by metis_tac[satis_def] >>
   `DEG (DIAM ff) <= i + 1` by fs[DEG_def] >>
   `¬satis M v (DIAM ff)` suffices_by metis_tac[] >> simp[satis_def] >>
   `!v''. M.frame.rel v v'' /\ v'' IN M.frame.world ==> ¬satis M v'' ff` suffices_by metis_tac[satis_def] >> rw[] >>
   simp[PULL_EXISTS] >>
   `∃form. DEG form ≤ i ∧ satis M' u' form ∧ ¬satis M v'' form` by metis_tac[] >>
   rw[partition_def,PULL_EXISTS] >>
   `form IN s` by (fs[Abbr`s`] >> qexists_tac `v''` >> rw[]) >>
   qexists_tac `form` >> rw[] >>
   `equiv form form` by metis_tac[equiv_REFL] >> `form IN {y | y ∈ s ∧ equiv form y}` by fs[] >>
   `{y | y ∈ s ∧ equiv form y} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
   `(CHOICE {y | y ∈ s ∧ equiv form y}) IN {y | y ∈ s ∧ equiv form y}` by metis_tac[CHOICE_DEF] >>
   fs[] >> 
   metis_tac[equiv_SYM,equiv_def]));
  





val (heightLE_rules, heightLE_ind, heightLE_cases) = Hol_reln`
  (!n. heightLE (M:'a model) x (M':'a model) x n) /\
  (!v. (!w. M.frame.rel w v ==> heightLE M x M' w n) ==>
       heightLE M x M' v (n + 1))
`;


val height_def = Define`height M x M' w = MIN_SET {n | heightLE M x M' w n}`;
                        
val model_height_def = Define`
model_height (M:'a model) x (M':'a model) = MAX_SET {n | ?w. w IN M.frame.world /\ height M x M' w = n}`;


val hrestriction_def = Define`
hrestriction M x M' n =
  <| frame := <| world := {w | w IN M.frame.world /\ height M x M' w <= n};
                 rel := λn1 n2. M.frame.rel n1 n2 |>;
     valt := λphi n. M.valt phi n |>`;

(*

val lemma_2_33 = store_thm(
"lemma_2_33",
``!M x M' k. rooted_model M x M' ==>
  !w. w IN (hrestriction M x M' k).frame.world ==> ?f. nbisim (hrestriction M x M' k) M f (k - height M x M' w) w w``,
rw[] >> qexists_tac `λn w1 w2. w1 = w2` >> rw[nbisim_def]
>- fs[hrestriction_def]
>- fs[satis_def,hrestriction_def,IN_DEF]
>- fs[hrestriction_def]
>- fs[hrestriction_def]
>- fs[hrestriction_def] >> fs[height_def] >> 

*)


(* finite model property via filtration *)

val CUS_def = Define`
CUS Σ <=> !f f'. ((DISJ f f') IN Σ ==> f IN Σ /\ f' IN Σ) /\
                 ((NOT f) IN Σ ==> f IN Σ) /\
                 ((DIAM f) IN Σ ==> f IN Σ)`;


val REL_CUS_def = Define`
REL_CUS Σ M = λw v. w IN M.frame.world /\
                    v IN M.frame.world /\
                    (!phi. phi IN Σ ==> (satis M w phi <=> satis M v phi))`;

val EC_CUS_def = Define`
EC_CUS Σ M w = {v | (REL_CUS Σ M) w v}`;

val EC_REP_def = Define`
EC_REP Σ M w = MIN_SET (EC_CUS Σ M w)`;

val EC_REP_SET_def = Define`
EC_REP_SET Σ M = {n | ?w. w IN M.frame.world /\ n = EC_REP Σ M w}`;

val IN_EC_CUS_IN_world = store_thm(
"IN_EC_CUS_IN_world",
``!x. x IN EC_CUS Σ M w ==> x IN M.frame.world``,
rpt strip_tac >> fs[EC_CUS_def,REL_CUS_def]);

val SAME_EC_SAME_tau = store_thm(
"SAME_EC_SAME_tau",
``!a b w. a IN EC_CUS Σ M w /\ b IN EC_CUS Σ M w ==> (!phi. phi IN Σ ==> (satis M a phi <=> satis M b phi))``,
rpt strip_tac >> fs[EC_CUS_def,REL_CUS_def]);



val REL_CUS_SYMM = store_thm(
"REL_CUS_SYMM",
``!w v. REL_CUS Σ M w v <=> REL_CUS Σ M v w``,
rpt strip_tac >> eq_tac >> strip_tac
>> fs[REL_CUS_def]);

val REL_CUS_REFL = store_thm(
"REL_CUS_REFL",
``!w. w IN M.frame.world ==> REL_CUS Σ M w w``,
gen_tac >> fs[REL_CUS_def]);

val REL_CUS_TRANS = store_thm(
"REL_CUS_TRANS",
``!u v w. u IN M.frame.world /\ v IN M.frame.world /\ w IN M.frame.world /\ REL_CUS Σ M u v /\ REL_CUS Σ M u w ==> REL_CUS Σ M v w``,
rpt strip_tac >> rw[REL_CUS_def] >>
`satis M u phi <=> satis M v phi` by metis_tac[REL_CUS_def] >>
`satis M u phi <=> satis M w phi` by metis_tac[REL_CUS_def] >> metis_tac[]);

val REL_EC = store_thm(
"REL_EC",
``!w v. w IN M.frame.world /\ v IN M.frame.world ==> (REL_CUS Σ M) w v ==> (EC_CUS Σ M w = EC_CUS Σ M v)``,
rpt strip_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
>- (`REL_CUS Σ M v x` suffices_by fs[EC_CUS_def] >>
`REL_CUS Σ M w x` by fs[EC_CUS_def] >>
`x IN M.frame.world` by fs[REL_CUS_def] >>
metis_tac[REL_CUS_TRANS])
>- (`REL_CUS Σ M w x` suffices_by fs[EC_CUS_def] >>
`REL_CUS Σ M v x` by fs[EC_CUS_def] >>
`x IN M.frame.world` by fs[REL_CUS_def] >> metis_tac[REL_CUS_SYMM,REL_CUS_TRANS]));

val EC_NOT_EMPTY = store_thm(
"EC_NOT_EMPTY",
``!w. w IN M.frame.world ==> EC_CUS Σ M w <> {}``,
rpt strip_tac >>
`w IN EC_CUS Σ M w` suffices_by metis_tac[MEMBER_NOT_EMPTY,EC_CUS_def] >>
`(REL_CUS Σ M) w w` by metis_tac[REL_CUS_REFL] >>
`w IN {v | (REL_CUS Σ M) w v}` by simp[] >> metis_tac[EC_CUS_def]);

val REP_IN_world = store_thm(
"REP_IN_world",
``w IN M.frame.world ==> EC_REP Σ M w IN M.frame.world``,
rpt strip_tac >>
fs[EC_REP_def] >> `MIN_SET (EC_CUS Σ M w) ∈ (EC_CUS Σ M w)` suffices_by metis_tac[IN_EC_CUS_IN_world] >>
`(EC_CUS Σ M w) <> {}` by metis_tac[EC_NOT_EMPTY] >> metis_tac[MIN_SET_LEM]);

val REP_IN_EC = store_thm(
"REP_IN_EC",
``!w. w IN M.frame.world ==> (EC_REP Σ M w) IN (EC_CUS Σ M w)``,
rw[] >> `EC_CUS Σ M w <> {}` by metis_tac[EC_NOT_EMPTY] >>
metis_tac[EC_REP_def,MIN_SET_LEM]);

val RESTRICT_tau_theory = Define`
RESTRICT_tau_theory Σ M w = {phi | phi IN Σ /\ satis M w phi}`;

val ELEM_IN_EC = store_thm(
"ELEM_IN_EC",
``!n. n IN M.frame.world ==> n IN EC_CUS Σ M n``,
rpt strip_tac >>
`(REL_CUS Σ M) n n` by metis_tac[REL_CUS_REFL] >>
`n IN {v | (REL_CUS Σ M) n v}` by simp[] >> metis_tac[EC_CUS_def]);

val REP_W_SAME_tau = store_thm(
"REP_W_SAME_tau",
``!phi w. (phi IN Σ /\ w IN M.frame.world) ==> (satis M (EC_REP Σ M w) phi <=> satis M w phi)``,
rpt strip_tac >>
`(EC_REP Σ M w) IN (EC_CUS Σ M w) /\ w IN (EC_CUS Σ M w)` suffices_by metis_tac[SAME_EC_SAME_tau] >> metis_tac[REP_IN_EC,ELEM_IN_EC]);

val EC_tau = store_thm(
"EC_tau",
``!n1 n2. n1 IN M.frame.world /\ n2 IN M.frame.world ==> (EC_CUS Σ M n1 = EC_CUS Σ M n2 ==>
RESTRICT_tau_theory Σ M n1 = RESTRICT_tau_theory Σ M n2)``,
rpt strip_tac >> simp[SET_EQ_SUBSET] >> simp[SUBSET_DEF] >> rpt strip_tac
>> simp[RESTRICT_tau_theory] >>
fs[RESTRICT_tau_theory] >>
`EC_CUS Σ M n1 ⊆ EC_CUS Σ M n2` by simp[SET_EQ_SUBSET] >> fs[SUBSET_DEF] >>
`n1 IN EC_CUS Σ M n1` by metis_tac[ELEM_IN_EC] >>
`n1 ∈ EC_CUS Σ M n2` by metis_tac[] >>
`REL_CUS Σ M n2 n1` by fs[EC_CUS_def] >>
metis_tac[REL_CUS_def]);

val tau_EC = store_thm(
"tau_EC",
``!n1 n2. n1 IN M.frame.world /\ n2 IN M.frame.world ==> (RESTRICT_tau_theory Σ M n1 = RESTRICT_tau_theory Σ M n2 ==> EC_CUS Σ M n1 = EC_CUS Σ M n2)``,
rpt strip_tac >> simp[SET_EQ_SUBSET] >> simp[SUBSET_DEF] >> rpt strip_tac
>- (simp[EC_CUS_def] >> simp[REL_CUS_def] >>
`x IN M.frame.world` by fs[EC_CUS_def,REL_CUS_def] >> rw[] >> eq_tac >> strip_tac
  >- (`RESTRICT_tau_theory Σ M n2  ⊆ RESTRICT_tau_theory Σ M n1` by simp[SET_EQ_SUBSET] >>
     `phi IN RESTRICT_tau_theory Σ M n2` by fs[RESTRICT_tau_theory] >>
     `phi IN RESTRICT_tau_theory Σ M n1` by metis_tac[SUBSET_DEF] >>
     `satis M n1 phi` by fs[RESTRICT_tau_theory] >>
     `REL_CUS Σ M n1 x` by fs[EC_CUS_def] >>
     metis_tac[REL_CUS_def])
  >- (`RESTRICT_tau_theory Σ M n1  ⊆ RESTRICT_tau_theory Σ M n2` by simp[SET_EQ_SUBSET] >> 
     `REL_CUS Σ M n1 x` by fs[EC_CUS_def] >>
     `satis M n1 phi` by metis_tac[REL_CUS_def] >>
     fs[SUBSET_DEF] >> fs[RESTRICT_tau_theory]))
>- (simp[EC_CUS_def] >> simp[REL_CUS_def] >>
`x IN M.frame.world` by fs[EC_CUS_def,REL_CUS_def] >> rw[] >> eq_tac >> strip_tac
  >- (`REL_CUS Σ M n2 x` by fs[EC_CUS_def] >>
     `RESTRICT_tau_theory Σ M n1 ⊆ RESTRICT_tau_theory Σ M n2` by metis_tac[SET_EQ_SUBSET] >> fs[SUBSET_DEF,RESTRICT_tau_theory] >>
     `satis M n2 phi` by metis_tac[] >>
     metis_tac[REL_CUS_def])
  >- (`REL_CUS Σ M n2 x` by fs[EC_CUS_def] >>
     `RESTRICT_tau_theory Σ M n2 ⊆ RESTRICT_tau_theory Σ M n1` by metis_tac[SET_EQ_SUBSET] >> fs[SUBSET_DEF,RESTRICT_tau_theory] >>
     `satis M n2 phi` by metis_tac[REL_CUS_def] >>
     metis_tac[]))
);

val SAME_REP_SAME_tau = store_thm(
"SAME_REP_SAME_tau",
``w IN M.frame.world /\ w' IN M.frame.world /\ EC_REP Σ M w = EC_REP Σ M w' ==>
(!phi. phi IN Σ ==> (satis M w phi <=> satis M w' phi))``,
rw[] >>
`EC_REP Σ M w IN EC_CUS Σ M w` by metis_tac[REP_IN_EC] >>
`w IN EC_CUS Σ M w` by metis_tac[ELEM_IN_EC] >>
`(satis M w phi <=> satis M (EC_REP Σ M w) phi)` by metis_tac[SAME_EC_SAME_tau] >>
`EC_REP Σ M w' IN EC_CUS Σ M w'` by metis_tac[REP_IN_EC] >>
`w' IN EC_CUS Σ M w'` by metis_tac[ELEM_IN_EC] >>
`(satis M w' phi <=> satis M (EC_REP Σ M w') phi)` by metis_tac[SAME_EC_SAME_tau] >>
metis_tac[]);

val SAME_REP_SAME_EC = store_thm(
"SAME_REP_SAME_EC",
``w IN M.frame.world /\ w' IN M.frame.world /\ EC_REP Σ M w = EC_REP Σ M w' ==> EC_CUS Σ M w = EC_CUS Σ M w'``,
rw[] >>
`(!phi. phi IN Σ ==> (satis M w phi <=> satis M w' phi))` by metis_tac[SAME_REP_SAME_tau] >>
`RESTRICT_tau_theory Σ M w = RESTRICT_tau_theory Σ M w'` by
(fs[RESTRICT_tau_theory] >> simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> metis_tac[]) >>
metis_tac[tau_EC]);

val filtration_def = Define`
filtration M Σ FLT <=>
CUS Σ /\
(FLT.frame.world = EC_REP_SET Σ M) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ M.frame.rel w v ==> FLT.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ FLT.frame.rel (EC_REP Σ M w) (EC_REP Σ M v) ==> (!phi psi. (phi IN Σ /\ phi = DIAM psi) ==> (satis M v psi ==> satis M w phi))) /\
(!p s. FLT.valt p s <=> (?w. s = EC_REP Σ M w /\ satis M w (VAR p)))`;

val FLT_M_world = store_thm(
"FLT_M_world",
``!w. filtration M Σ FLT /\ w IN FLT.frame.world ==> w IN M.frame.world``,
rpt strip_tac >>
`w IN EC_REP_SET Σ M` by metis_tac[filtration_def] >>
fs[EC_REP_SET_def] >> fs[EC_REP_def] >>
`EC_CUS Σ M w' <> {}` by metis_tac[EC_NOT_EMPTY] >>
`MIN_SET (EC_CUS Σ M w') IN (EC_CUS Σ M w')` by metis_tac[MIN_SET_LEM] >>
`(EC_CUS Σ M w') ⊆ M.frame.world` by
(rw[SUBSET_DEF] >>
`REL_CUS Σ M w' x` by fs[EC_CUS_def] >>
metis_tac[REL_CUS_def]) >>
metis_tac[SUBSET_DEF]);


val EC_CUS_SUBSET_W = store_thm(
"EC_CUS_SUBSET_W",
``!w. w IN M.frame.world ==> EC_CUS Σ M w ⊆ M.frame.world``,
rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
`REL_CUS Σ M w x` by fs[EC_CUS_def] >> metis_tac[REL_CUS_def]);

val filtration_REP_REFL = store_thm(
"filtration_REP_REFL",
``filtration M Σ FLT ==> (!w. w IN FLT.frame.world ==> w = MIN_SET (EC_CUS Σ M w))``,
rpt strip_tac >>
`w IN EC_REP_SET Σ M` by metis_tac[filtration_def] >> fs[EC_REP_SET_def] >>
fs[EC_REP_def] >>
`EC_CUS Σ M w' = EC_CUS Σ M (MIN_SET (EC_CUS Σ M w'))` suffices_by metis_tac[] >>
`EC_CUS Σ M w' <> {}` by metis_tac[EC_NOT_EMPTY] >>
`w IN (EC_CUS Σ M w')` by metis_tac[MIN_SET_LEM] >>
`w IN M.frame.world` by metis_tac[EC_CUS_SUBSET_W,SUBSET_DEF] >>
`REL_CUS Σ M w' (MIN_SET (EC_CUS Σ M w'))` suffices_by metis_tac[REL_EC] >>
`!a. a IN (EC_CUS Σ M w') ==> REL_CUS Σ M w' a` by
(rpt strip_tac >> fs[EC_CUS_def]) >> metis_tac[]);

val prop_2_38_lemma = store_thm(
"prop_2_38_lemma",
``!Σ M. FINITE Σ /\ filtration M Σ FLT ==> ?f. INJ f (FLT.frame.world) (POW Σ)``,
rpt strip_tac >>
qexists_tac `λw. RESTRICT_tau_theory Σ M w` >> rw[INJ_DEF]
>- (rw[POW_DEF] >> rw[RESTRICT_tau_theory] >> simp[SUBSET_DEF])
>- (`w = MIN_SET (EC_CUS Σ M w)` by metis_tac[filtration_REP_REFL] >>
`w' = MIN_SET (EC_CUS Σ M w')` by metis_tac[filtration_REP_REFL] >>
`w IN M.frame.world` by metis_tac[FLT_M_world] >>
`w' IN M.frame.world` by metis_tac[FLT_M_world] >>
`EC_CUS Σ M w = EC_CUS Σ M w'` by metis_tac[tau_EC] >> metis_tac[]));


val prop_2_38 = store_thm(
"prop_2_38",
``!Σ M FLT. FINITE Σ /\ filtration M Σ FLT ==> CARD (FLT.frame.world) <= 2 ** (CARD (Σ))``,
rpt strip_tac >>
`CARD (POW Σ) = 2 ** CARD Σ` by simp[CARD_POW] >>
`CARD FLT.frame.world ≤ CARD (POW Σ)` suffices_by rw[] >>
irule INJ_CARD
>- metis_tac[FINITE_POW]
>- metis_tac[prop_2_38_lemma]);

val thm_2_39 = store_thm(
"thm_2_39",
``!phi. phi IN Σ ==> (!w. w IN M.frame.world /\ filtration M Σ FLT ==> (satis M w phi <=> satis FLT (EC_REP Σ M w) phi))``,
gen_tac >> strip_tac >> Induct_on `phi`
>- (rw[satis_def] >> eq_tac >> rpt strip_tac
  >- (`EC_REP Σ M w ∈ EC_REP_SET Σ M ` suffices_by metis_tac[filtration_def] >>
     fs[EC_REP_SET_def] >> qexists_tac `w` >> metis_tac[])
  >- (`FLT.valt a (EC_REP Σ M w)` suffices_by fs[IN_DEF] >>
     `∃w'. (EC_REP Σ M w) = EC_REP Σ M w' ∧ satis M w' (VAR a)` suffices_by fs[filtration_def] >>
     qexists_tac `w` >>
     metis_tac[satis_def,IN_DEF])
  >- (`FLT.valt a (EC_REP Σ M w)` by fs[IN_DEF] >>
     `∃w'. (EC_REP Σ M w) = EC_REP Σ M w' ∧ satis M w' (VAR a)` by metis_tac[filtration_def] >>
     `w' IN M.frame.world` by metis_tac[satis_def] >>
     `EC_CUS Σ M w = EC_CUS Σ M w'` by metis_tac[SAME_REP_SAME_EC] >>
     `w IN EC_CUS Σ M w` by metis_tac[ELEM_IN_EC] >>
     `w' IN EC_CUS Σ M w'` by metis_tac[ELEM_IN_EC] >>
     `w' IN EC_CUS Σ M w` by metis_tac[] >>
     `satis M w (VAR a)` by metis_tac[SAME_EC_SAME_tau] >> metis_tac[satis_def,IN_DEF]))
>- (rw[satis_def] >> eq_tac >> rw[]
  >> `CUS Σ` by metis_tac[filtration_def] >> fs[CUS_def] >>
     `phi IN Σ /\ phi' IN Σ` by metis_tac[] >> metis_tac[])
>- rw[satis_def]
>- (rw[satis_def] >> eq_tac >> rw[]
  >> `CUS Σ` by metis_tac[filtration_def] >> fs[CUS_def] >>
  `EC_REP Σ M w IN EC_REP_SET Σ M` by (fs[EC_REP_SET_def] >> qexists_tac `w` >> metis_tac[]) >>
  metis_tac[filtration_def])
>- (rw[satis_def] >> eq_tac >> rw[]
  >- (`EC_REP Σ M w IN EC_REP_SET Σ M` by (fs[EC_REP_SET_def] >> qexists_tac `w` >> metis_tac[]) >>
  metis_tac[filtration_def])
  >- (`M.frame.rel w v` by fs[IN_DEF] >>
     `FLT.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)` by metis_tac[filtration_def] >>
     `EC_REP Σ M v IN EC_REP_SET Σ M` by (fs[EC_REP_SET_def] >> qexists_tac `v` >> metis_tac[]) >>
     `EC_REP Σ M v IN FLT.frame.world` by metis_tac[filtration_def] >>
     qexists_tac `EC_REP Σ M v` >> rw[] 
     >> (`CUS Σ` by metis_tac[filtration_def] >>
        `phi IN Σ` by metis_tac[CUS_def] >> metis_tac[]))
  >- (`CUS Σ` by metis_tac[filtration_def] >>
     `phi IN Σ` by metis_tac[CUS_def] >>
     `v IN EC_REP_SET Σ M` by metis_tac[filtration_def] >>
     fs[EC_REP_SET_def] >>
     `satis M w' phi` by metis_tac[] >>
     `satis M w (DIAM phi)` suffices_by metis_tac[satis_def] >>
     `FLT.frame.rel (EC_REP Σ M w) (EC_REP Σ M w')` by fs[IN_DEF] >> metis_tac[filtration_def])));

val FLT_def = Define`
FLT M Σ = <| frame := <| world := EC_REP_SET Σ M ;
                         rel := λn1 n2.
                         ?w1 w2.
                         (w1 IN M.frame.world /\ w2 IN M.frame.world /\
                         n1 = EC_REP Σ M w1 /\ n2 = EC_REP Σ M w2 /\
                         ?w' v'. w' IN M.frame.world /\ v' IN M.frame.world /\
                         w' IN EC_CUS Σ M w1 /\ v' IN EC_CUS Σ M w2 /\ M.frame.rel w' v') |>;
             valt := λp s. ∃w. s = EC_REP Σ M w ∧ satis M w (VAR p) |>`;
     
     
val FLT_EXISTS = store_thm(
"FLT_EXISTS",
``!M Σ. CUS Σ ==> filtration M Σ (FLT M Σ)``,
rw[filtration_def] >- fs[FLT_def]
>- (fs[FLT_def] >> map_every qexists_tac [`w`,`v`] >> rw[] >> map_every qexists_tac [`w`,`v`] >> rw[] >> metis_tac[ELEM_IN_EC])
>- (fs[FLT_def] >>
   `psi IN Σ` by fs[CUS_def] >>
   `satis M v psi ⇔ satis M w2 psi` by metis_tac[SAME_REP_SAME_tau] >>
   `satis M v' psi ⇔ satis M w2 psi` by (`w2 IN EC_CUS Σ M w2` by metis_tac[ELEM_IN_EC] >> metis_tac[SAME_EC_SAME_tau]) >>
   `satis M v' psi` by metis_tac[] >>
   `satis M w' (DIAM psi)` by (rw[satis_def] >> qexists_tac `v'` >> fs[IN_DEF]) >>
   `satis M w (DIAM psi) ⇔ satis M w1 (DIAM psi)` by metis_tac[SAME_REP_SAME_tau] >>
   `satis M w' (DIAM psi) ⇔ satis M w1 (DIAM psi)` by (`w1 IN EC_CUS Σ M w1` by metis_tac[ELEM_IN_EC] >> metis_tac[SAME_EC_SAME_tau]) >> metis_tac[])
>- fs[FLT_def]);


val subforms_def = Define`
  subforms (VAR a) = {VAR a} /\
  subforms (FALSE) = {FALSE} /\
  subforms (NOT f) = NOT f INSERT subforms f /\
  subforms (DISJ f1 f2) = DISJ f1 f2 INSERT subforms f1 UNION subforms f2 /\
  subforms (DIAM f) = DIAM f INSERT subforms f
  `;

val subforms_phi_phi = store_thm(
"subforms_phi_phi",
``!phi. phi IN subforms phi``,
Induct_on `phi` >> fs[subforms_def]);

val subforms_DISJ = store_thm(
"subforms_DISJ",
``f1 IN (subforms (DISJ f1 f2)) /\ f2 IN (subforms (DISJ f1 f2))``,
rw[subforms_def,subforms_phi_phi]);

val subforms_NOT = store_thm(
"subforms_NOT",
``f IN (subforms (NOT f))``,
rw[subforms_def,subforms_phi_phi]);

val subforms_DIAM = store_thm(
"subforms_DIAM",
``f IN (subforms (DIAM f))``,
rw[subforms_def,subforms_phi_phi]);

val subforms_trans = store_thm(
"subforms_trans",
``!f. f IN subforms phi /\ phi IN subforms psi ==> f IN subforms psi``,
rw[] >> Induct_on `psi` >> rw[] >> fs[subforms_def] 
>> fs[subforms_def]);



val subforms_phi_CUS = store_thm(
"subforms_phi_CUS",
``!phi. CUS (subforms phi)``,
rw[CUS_def] >> fs[subforms_def,UNION_DEF]
>- (`f IN (subforms (DISJ f f'))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f' IN (subforms (DISJ f f'))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f IN (subforms (NOT f))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f IN (subforms (DIAM f))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans]));

val subforms_FINITE = store_thm(
"subforms_FINITE",
``FINITE (subforms phi)``,
Induct_on `phi` >> fs[subforms_def]);

val thm_2_41 = store_thm(
  "thm_2_41",
``!phi. satis M w phi ==> ?M' w'. w' IN M'.frame.world /\ satis M' w' phi /\ FINITE (M'.frame.world)``,
rw[] >> qexists_tac `FLT M (subforms phi)` >> qexists_tac `EC_REP (subforms phi) M w` >> rw[]
>- (`w IN M.frame.world` by metis_tac[satis_in_world] >> fs[FLT_def,EC_REP_SET_def] >> qexists_tac `w` >> fs[])
>- (`CUS (subforms phi)` by metis_tac[subforms_phi_CUS] >>
   `filtration M (subforms phi) (FLT M (subforms phi))` by metis_tac[FLT_EXISTS] >>
   `phi IN (subforms phi)` by metis_tac[subforms_phi_phi] >>
   `w IN M.frame.world` by metis_tac[satis_in_world] >>
   metis_tac[thm_2_39])
>- (`CUS (subforms phi)` by metis_tac[subforms_phi_CUS] >>
   `filtration M (subforms phi) (FLT M (subforms phi))` by metis_tac[FLT_EXISTS] >>
   `FINITE (subforms phi)` by metis_tac[subforms_FINITE] >> 
   `CARD (FLT M (subforms phi)).frame.world ≤ 2 ** CARD (subforms phi)` by metis_tac[prop_2_38] >>

   drule_all (GEN_ALL prop_2_38_lemma) >> strip_tac >>
   imp_res_tac FINITE_INJ >> rfs[FINITE_POW]));
  

val _ = export_theory();