open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open equiv_on_partitionTheory;
open IBCDNFrevisedTheory;
open prim_recTheory;
open listTheory pairTheory;


val _ = new_theory "chap2_3";

val irule = fn th => irule th >> rpt conj_tac
(* finite model property via selection *)


val DEG_def =  Define
    `DEG (VAR p) = 0 /\
     DEG (FALSE) = 0 /\
     DEG (NOT form) = DEG form /\
     DEG (DISJ form1 form2) = MAX (DEG form1) (DEG form2) /\
     DEG (DIAM form) = (DEG form) + 1`;


val DEG_0_propform = store_thm(
"DEG_0_propform",
``!f. DEG f = 0 <=> propform f``,
Induct_on `f` >> fs[DEG_def,propform_def]);


(* base case *)

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

val subforms_FINITE = store_thm(
"subforms_FINITE",
``FINITE (subforms phi)``,
Induct_on `phi` >> fs[subforms_def]);






(* FMP via filtratition *)



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
EC_REP Σ M w = CHOICE (EC_CUS Σ M w)`;

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
  fs[EC_REP_def,EC_CUS_def,REL_CUS_def] >>
  `(CHOICE {v | v ∈ M.frame.world ∧ ∀phi. phi ∈ Σ ⇒ (satis M w phi ⇔ satis M v phi)}) IN
  {v | v ∈ M.frame.world ∧ ∀phi. phi ∈ Σ ⇒ (satis M w phi ⇔ satis M v phi)}`
    by (`{v | v ∈ M.frame.world ∧ ∀phi. phi ∈ Σ ⇒ (satis M w phi ⇔ satis M v phi)} <> {}`
            suffices_by metis_tac[CHOICE_DEF] >>
        `w IN {v | v ∈ M.frame.world ∧ ∀phi. phi ∈ Σ ⇒ (satis M w phi ⇔ satis M v phi)}`
            suffices_by metis_tac[MEMBER_NOT_EMPTY] >> fs[]) >>
  fs[]);


val REP_IN_EC = store_thm(
  "REP_IN_EC",
  ``!w. w IN M.frame.world ==> (EC_REP Σ M w) IN (EC_CUS Σ M w)``,
  rw[] >> `EC_CUS Σ M w <> {}` by metis_tac[EC_NOT_EMPTY] >> metis_tac[EC_REP_def,CHOICE_DEF]);


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
filtration M Σ FL <=>
CUS Σ /\
(FL.frame.world = EC_REP_SET Σ M) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ M.frame.rel w v ==> FL.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)) /\
(!w v. w IN M.frame.world /\ v IN M.frame.world /\ FL.frame.rel (EC_REP Σ M w) (EC_REP Σ M v) ==> (!phi psi. (phi IN Σ /\ phi = DIAM psi) ==> (satis M v psi ==> satis M w phi))) /\
(!p s. FL.valt p s <=> (?w. s = EC_REP Σ M w /\ satis M w (VAR p)))`;

val FLT_M_world = store_thm(
"FLT_M_world",
``!w. filtration M Σ FL /\ w IN FL.frame.world ==> w IN M.frame.world``,
rpt strip_tac >>
`w IN EC_REP_SET Σ M` by metis_tac[filtration_def] >>
fs[EC_REP_SET_def] >> fs[EC_REP_def] >>
`EC_CUS Σ M w' <> {}` by metis_tac[EC_NOT_EMPTY] >>
`(CHOICE (EC_CUS Σ M w')) IN (EC_CUS Σ M w')` by metis_tac[CHOICE_DEF] >>
`(EC_CUS Σ M w') SUBSET M.frame.world` suffices_by fs[SUBSET_DEF] >>
rw[EC_CUS_def,REL_CUS_def] >> fs[SUBSET_DEF]);


val EC_CUS_SUBSET_W = store_thm(
"EC_CUS_SUBSET_W",
``!w. w IN M.frame.world ==> EC_CUS Σ M w ⊆ M.frame.world``,
rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
`REL_CUS Σ M w x` by fs[EC_CUS_def] >> metis_tac[REL_CUS_def]);

val filtration_REP_REFL = store_thm(
"filtration_REP_REFL",
``filtration M Σ FL ==> (!w. w IN FL.frame.world ==> w = CHOICE (EC_CUS Σ M w))``,
rpt strip_tac >>
`w IN EC_REP_SET Σ M` by metis_tac[filtration_def] >> fs[EC_REP_SET_def] >>
fs[EC_REP_def] >>
`EC_CUS Σ M w' = EC_CUS Σ M (CHOICE (EC_CUS Σ M w'))` suffices_by metis_tac[] >>
`EC_CUS Σ M w' <> {}` by metis_tac[EC_NOT_EMPTY] >>
`w IN (EC_CUS Σ M w')` by metis_tac[CHOICE_DEF] >>
`w IN M.frame.world` by metis_tac[EC_CUS_SUBSET_W,SUBSET_DEF] >>
`REL_CUS Σ M w' (CHOICE (EC_CUS Σ M w'))` suffices_by metis_tac[REL_EC] >>
`!a. a IN (EC_CUS Σ M w') ==> REL_CUS Σ M w' a` by
(rpt strip_tac >> fs[EC_CUS_def]) >> metis_tac[]);

val prop_2_38_lemma = store_thm(
"prop_2_38_lemma",
``!Σ M. FINITE Σ /\ filtration M Σ FL ==> ?f. INJ f (FL.frame.world) (POW Σ)``,
rpt strip_tac >>
qexists_tac `λw. RESTRICT_tau_theory Σ M w` >> rw[INJ_DEF]
>- (rw[POW_DEF] >> rw[RESTRICT_tau_theory] >> simp[SUBSET_DEF])
>- (`w = CHOICE (EC_CUS Σ M w)` by metis_tac[filtration_REP_REFL] >>
`w' = CHOICE (EC_CUS Σ M w')` by metis_tac[filtration_REP_REFL] >>
`w IN M.frame.world` by metis_tac[FLT_M_world] >>
`w' IN M.frame.world` by metis_tac[FLT_M_world] >>
`EC_CUS Σ M w = EC_CUS Σ M w'` by metis_tac[tau_EC] >> metis_tac[]));


val prop_2_38 = store_thm(
"prop_2_38",
``!Σ M FL. FINITE Σ /\ filtration M Σ FL ==> CARD (FL.frame.world) <= 2 ** (CARD (Σ))``,
rpt strip_tac >>
`CARD (POW Σ) = 2 ** CARD Σ` by simp[CARD_POW] >>
`CARD FL.frame.world ≤ CARD (POW Σ)` suffices_by rw[] >>
irule INJ_CARD
>- metis_tac[FINITE_POW]
>- metis_tac[prop_2_38_lemma]);

val thm_2_39 = store_thm(
"thm_2_39",
``!phi. phi IN Σ ==> (!w. w IN M.frame.world /\ filtration M Σ FL ==> (satis M w phi <=> satis FL (EC_REP Σ M w) phi))``,
gen_tac >> strip_tac >> Induct_on `phi`
>- (rw[satis_def] >> eq_tac >> rpt strip_tac
  >- (`EC_REP Σ M w ∈ EC_REP_SET Σ M ` suffices_by metis_tac[filtration_def] >>
     fs[EC_REP_SET_def] >> qexists_tac `w` >> metis_tac[])
  >- (`FL.valt n (EC_REP Σ M w)` suffices_by fs[IN_DEF] >>
     `∃w'. (EC_REP Σ M w) = EC_REP Σ M w' ∧ satis M w' (VAR n)` suffices_by fs[filtration_def] >>
     qexists_tac `w` >>
     metis_tac[satis_def,IN_DEF])
  >- (`FL.valt n (EC_REP Σ M w)` by fs[IN_DEF] >>
     `∃w'. (EC_REP Σ M w) = EC_REP Σ M w' ∧ satis M w' (VAR n)` by metis_tac[filtration_def] >>
     `w' IN M.frame.world` by metis_tac[satis_def] >>
     `EC_CUS Σ M w = EC_CUS Σ M w'` by metis_tac[SAME_REP_SAME_EC] >>
     `w IN EC_CUS Σ M w` by metis_tac[ELEM_IN_EC] >>
     `w' IN EC_CUS Σ M w'` by metis_tac[ELEM_IN_EC] >>
     `w' IN EC_CUS Σ M w` by metis_tac[] >>
     `satis M w (VAR n)` by metis_tac[SAME_EC_SAME_tau] >> metis_tac[satis_def,IN_DEF]))
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
     `FL.frame.rel (EC_REP Σ M w) (EC_REP Σ M v)` by metis_tac[filtration_def] >>
     `EC_REP Σ M v IN EC_REP_SET Σ M` by (fs[EC_REP_SET_def] >> qexists_tac `v` >> metis_tac[]) >>
     `EC_REP Σ M v IN FL.frame.world` by metis_tac[filtration_def] >>
     qexists_tac `EC_REP Σ M v` >> rw[]
     >> (`CUS Σ` by metis_tac[filtration_def] >>
        `phi IN Σ` by metis_tac[CUS_def] >> metis_tac[]))
  >- (`CUS Σ` by metis_tac[filtration_def] >>
     `phi IN Σ` by metis_tac[CUS_def] >>
     `v IN EC_REP_SET Σ M` by metis_tac[filtration_def] >>
     fs[EC_REP_SET_def] >>
     `satis M w' phi` by metis_tac[] >>
     `satis M w (DIAM phi)` suffices_by metis_tac[satis_def] >>
     `FL.frame.rel (EC_REP Σ M w) (EC_REP Σ M w')` by fs[IN_DEF] >> metis_tac[filtration_def])));

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


Theorem Rs_preserves_SYMM:
!M Σ. CUS Σ ==>
      (!a b.
         (a IN M.frame.world /\ b IN M.frame.world /\ M.frame.rel a b) ==>
              M.frame.rel b a) ==>
      (!fa fb. fa IN (FLT M Σ).frame.world /\ fb IN (FLT M Σ).frame.world /\
               (FLT M Σ).frame.rel fa fb ==> (FLT M Σ).frame.rel fb fa)

Proof
 rw[] >> fs[FLT_def,PULL_EXISTS] >>
 map_every qexists_tac [`w2`,`w1`,`v'`,`w'`] >> rw[]
QED


val subforms_phi_CUS = store_thm(
"subforms_phi_CUS",
``!phi. CUS (subforms phi)``,
rw[CUS_def] >> fs[subforms_def,UNION_DEF]
>- (`f IN (subforms (DISJ f f'))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f' IN (subforms (DISJ f f'))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f IN (subforms (NOT f))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans])
>- (`f IN (subforms (DIAM f))` by (fs[subforms_def] >> metis_tac[subforms_phi_phi]) >> metis_tac[subforms_trans]));



val thm_2_41 = store_thm(
  "thm_2_41",
``!phi M w. satis M (w:'b) phi ==> ?M' w':'b. w' IN M'.frame.world /\ satis M' w' phi /\ FINITE (M'.frame.world)``,
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


val REL_2_42_def = Define`
    REL_2_42 Σ M = \a b. ?w. w IN M.frame.world /\ a = EC_CUS Σ M w /\
                         ?v. v IN M.frame.world /\ b = EC_CUS Σ M v /\
                         (!phi. (DIAM phi) IN Σ /\ satis M v (DISJ phi (DIAM phi)) ==> satis M w (DIAM phi))`;


val thm_2_42_ii = store_thm(
  "thm_2_42_ii",
  ``!M. (!u v w. u IN M.frame.world /\ v IN M.frame.world /\ w IN M.frame.world
                   ==> M.frame.rel u v /\ M.frame.rel v w ==> M.frame.rel u w)
          ==> !Σ. CUS Σ
            ==> !a b c. (REL_2_42 Σ M) a b /\ (REL_2_42 Σ M) b c
                          ==> (REL_2_42 Σ M) a c``,
  rw[] >> fs[REL_2_42_def,PULL_EXISTS] >> map_every qexists_tac [`w`,`v'`] >> rw[] >>
  `satis M w' (◇ phi)` by metis_tac[] >>
  `satis M v (DIAM phi)`
      by (`!form. form IN Σ ==> satis M w' form ==> satis M v form` suffices_by metis_tac[] >>
         rw[] >> fs[EXTENSION] >>
         fs[EC_CUS_def,REL_CUS_def] >> metis_tac[]) >>
  metis_tac[satis_def]);


val ELEM_EC_CUS = store_thm(
  "ELEM_EC_CUS",
  ``!a. a IN EC_CUS Σ M w ==> EC_CUS Σ M w = EC_CUS Σ M a``,
  rw[EC_CUS_def,EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
  >- (`REL_CUS Σ M x w` by metis_tac[REL_CUS_SYMM] >>
     `x IN M.frame.world /\ a IN M.frame.world /\ w IN M.frame.world` by metis_tac[REL_CUS_def] >>
     `REL_CUS Σ M x a` by metis_tac[REL_CUS_TRANS] >>
     metis_tac[REL_CUS_SYMM])
  >- metis_tac[REL_CUS_TRANS,REL_CUS_def]);




val thm_2_42_i = store_thm(
  "thm_2_42_i",
  ``!M. (!u v w. u IN M.frame.world /\ v IN M.frame.world /\ w IN M.frame.world
                   ==> M.frame.rel u v /\ M.frame.rel v w ==> M.frame.rel u w)
          ==> !Σ. CUS Σ
            ==> filtration M Σ <| frame := <| world := EC_REP_SET Σ M;
                                                rel := \w1 w2. REL_2_42 Σ M (EC_CUS Σ M w1) (EC_CUS Σ M w2)|>;
                                   valt := \p s. ?w. s = EC_REP Σ M w /\ satis M w (VAR p) |>``,
  rw[filtration_def,REL_2_42_def] (* 2 *)
  >- (simp[PULL_EXISTS] >> map_every qexists_tac [`w`,`v`] >> rw[] (* 3 *)
     >- (`w IN (EC_CUS Σ M w)` by rw[EC_CUS_def,REL_CUS_def] >>
        `(EC_CUS Σ M w) <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
        `(EC_REP Σ M w) IN (EC_CUS Σ M w)` by metis_tac[CHOICE_DEF,EC_REP_def] >>
        metis_tac[ELEM_EC_CUS])
     >- (`v IN (EC_CUS Σ M v)` by rw[EC_CUS_def,REL_CUS_def] >>
        `(EC_CUS Σ M v) <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
        `(EC_REP Σ M v) IN (EC_CUS Σ M v)` by metis_tac[CHOICE_DEF,EC_REP_def] >>
        metis_tac[ELEM_EC_CUS])
     >- (fs[satis_def] (* 2 *)
        >- (qexists_tac `v` >> rw[])
        >- (qexists_tac `v'` >> metis_tac[])))
  >- (fs[CUS_def] >> `psi IN Σ` by metis_tac[] >>
     `(satis M (EC_REP Σ M v) psi)` by metis_tac[REP_W_SAME_tau] >>
     `v' IN (EC_CUS Σ M v')` by (rw[EC_CUS_def] >> metis_tac[REL_CUS_REFL]) >>
     `v IN (EC_CUS Σ M v)` by (rw[EC_CUS_def] >> metis_tac[REL_CUS_REFL]) >>
     `EC_CUS Σ M v <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
     `(EC_REP Σ M v) IN (EC_CUS Σ M v)` by metis_tac[EC_REP_def,CHOICE_DEF] >>
     `EC_CUS Σ M (EC_REP Σ M v) = EC_CUS Σ M v` by metis_tac[ELEM_EC_CUS] >>
     `v' IN (EC_CUS Σ M v)` by metis_tac[] >>
     `satis M v' psi` by metis_tac[SAME_EC_SAME_tau] >>
     `satis M v' (DISJ psi (◇ psi))` by metis_tac[satis_def] >>
     `satis M w' (DIAM psi)` by metis_tac[] >>
     `w IN (EC_CUS Σ M w)` by (rw[EC_CUS_def] >> metis_tac[REL_CUS_REFL]) >>
     `EC_CUS Σ M w <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
     `(EC_REP Σ M w) IN (EC_CUS Σ M w)` by metis_tac[EC_REP_def,CHOICE_DEF] >>
     `EC_CUS Σ M (EC_REP Σ M w) = EC_CUS Σ M w` by metis_tac[ELEM_EC_CUS] >>
     fs[] >>
     `w' IN (EC_CUS Σ M w')` by (rw[EC_CUS_def] >> metis_tac[REL_CUS_REFL]) >>
     `w' IN EC_CUS Σ M w` by metis_tac[] >>
     metis_tac[SAME_EC_SAME_tau]));


val cluster_def = Define`
  cluster C FRM <=> C SUBSET FRM.world /\
                    (RESTRICT FRM.rel C) equiv_on FRM.world /\
                    (!D. C SUBSET D /\ C <> D ==> ¬((RESTRICT FRM.rel D) equiv_on FRM.world))`;

val simple_cluster_def = Define`
  simple_cluster C FRM <=> cluster C FRM /\ ?x. x IN FRM.world /\ C = {x}`;

val proper_cluster_def = Define`
  proper_cluster C FRM <=> cluster C FRM /\ ?x y. x IN C /\ y IN C /\ x <> y`;

(* FMP via selection *)


val peval_satis_strengthen = store_thm(
"peval_satis_strengthen",
``!M w f. propform f /\
          (∀a. VAR a ∈ subforms f ⇒ a ∈ s) /\ w IN M.frame.world ==> (satis M w f <=> peval ((λa. w IN M.valt a) INTER s) f)``,
Induct_on `f` >> rw[]
>- (`(VAR n) IN subforms (VAR n)` by fs[subforms_def] >>
   `n IN s` by fs[] >> metis_tac[satis_def])
>- (simp[satis_def] >>
   `(∀a. VAR a ∈ subforms f ⇒ a ∈ s)`
          by (`∀a. VAR a ∈ subforms f ⇒ (VAR a) IN subforms (DISJ f f')` suffices_by metis_tac[] >>
              `f IN (subforms (DISJ f f'))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >>
   `(∀a. VAR a ∈ subforms f' ⇒ a ∈ s)`
          by (`∀a. VAR a ∈ subforms f' ⇒ (VAR a) IN subforms (DISJ f f')` suffices_by metis_tac[] >>
              `f' IN (subforms (DISJ f f'))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >> metis_tac[])
>- metis_tac[satis_def]
>- (simp[satis_def] >>
   `(∀a. VAR a ∈ subforms f ⇒ a ∈ s)`
          by (`∀a. VAR a ∈ subforms f ⇒ (VAR a) IN subforms (¬f)` suffices_by metis_tac[] >>
              `f IN (subforms (¬f))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >> metis_tac[]));


val equiv0_peval_strengthen = store_thm(
"equiv0_peval_strengthen",
``!f1 f2. propform f1 /\ propform f2 /\
(∀a. VAR a ∈ subforms f1 ⇒ a ∈ s) /\
(∀a. VAR a ∈ subforms f2 ⇒ a ∈ s) ==>
(!σ. σ IN (POW s) ==> peval σ f1 = peval σ f2) ==> (!M w. satis M w f1 <=> satis M w f2)``,
rw[] >> eq_tac >> rw[] >> `w IN M.frame.world` by metis_tac[satis_in_world]
>- (`peval ((λa. w IN M.valt a) INTER s) f2` suffices_by metis_tac[peval_satis_strengthen,satis_in_world] >>
   `peval ((λa. w IN M.valt a) INTER s) f1` by metis_tac[peval_satis_strengthen] >>
   `((λa. w IN M.valt a) INTER s) IN (POW s)` by fs[POW_DEF,INTER_DEF,SUBSET_DEF] >>
   metis_tac[])
>- (`peval ((λa. w IN M.valt a) INTER s) f1` suffices_by metis_tac[peval_satis_strengthen,satis_in_world] >>
   `peval ((λa. w IN M.valt a) INTER s) f2` by metis_tac[peval_satis_strengthen] >>
   `((λa. w IN M.valt a) INTER s) IN (POW s)` by fs[POW_DEF,INTER_DEF,SUBSET_DEF] >>
   metis_tac[]));



val peval_restriction = store_thm(
  "peval_restriction",
  ``!f. propform f ==> (∀a. VAR a ∈ subforms f ⇒ a ∈ s) ==> !σ. peval σ f = peval (σ INTER s) f``,
  Induct_on `f`
  >- (rw[] >>
     `(VAR n) ∈ subforms (VAR n)`  by fs[subforms_def] >>
     `n IN s` by fs[] >> fs[IN_DEF])
  >- (rw[] >>
     `(∀a. VAR a ∈ subforms f' ⇒ a ∈ s)`
         by (`∀a. VAR a ∈ subforms f' ⇒ (VAR a) IN subforms (DISJ f f')` suffices_by metis_tac[] >>
              `f' IN (subforms (DISJ f f'))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >>
     `(∀a. VAR a ∈ subforms f ⇒ a ∈ s)`
         by (`∀a. VAR a ∈ subforms f ⇒ (VAR a) IN subforms (DISJ f f')` suffices_by metis_tac[] >>
              `f IN (subforms (DISJ f f'))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >>
     metis_tac[])
  >- fs[peval_def]
  >- (rw[] >>
   `(∀a. VAR a ∈ subforms f ⇒ a ∈ s)`
       by (`∀a. VAR a ∈ subforms f ⇒ (VAR a) IN subforms (¬f)` suffices_by metis_tac[] >>
              `f IN (subforms (¬f))` by fs[subforms_def,subforms_phi_phi] >>
              metis_tac[subforms_trans]) >> metis_tac[])
  >- fs[propform_def]);


val peval_satis = store_thm(
"peval_satis",
``!M w f. propform f /\ w IN M.frame.world ==> (satis M w f <=> peval (λa. w IN M.valt a) f)``,
Induct_on `f` >> rw[]
>> metis_tac[satis_def]);

val peval_equiv0 = store_thm(
"peval_equiv0",
``!f1 f2. propform f1 /\ propform f2 /\ (!M w:β. satis M w f1 <=> satis M w f2) ==> (!σ. peval σ f1 = peval σ f2)``,
gen_tac >> gen_tac >> strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
`?σ. (peval σ f1 /\ ¬(peval σ f2)) \/ (¬(peval σ f1) /\ peval σ f2)` by metis_tac[]
>- (`?M w:β. satis M w f1 /\ ¬satis M w f2` suffices_by metis_tac[] >>
    `(univ(:'b)) <> {}` by metis_tac[UNIV_NOT_EMPTY] >>
    `?b. b IN univ(:'b)` by metis_tac[MEMBER_NOT_EMPTY] >>
   qexists_tac `<| frame := <| world := {b};
                           rel := λn1 n2. (n1 = b /\ n2 = b) |>;
                   valt := λa w. (σ a) |>` >>
   qabbrev_tac `M = <| frame := <| world := {b};
                           rel := λn1 n2. (n1 = b /\ n2 = b) |>;
                   valt := λa w. (σ a) |>` >>
   qexists_tac `b` >> rw[]
   >- (`satis M b f1` suffices_by metis_tac[] >>
      `b IN M.frame.world` by fs[Abbr`M`] >>
      `peval (λa. b ∈ M.valt a) f1` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])
   >- (`b IN M.frame.world` by fs[Abbr`M`] >>
      `¬(peval (λa. b ∈ M.valt a) f2)` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[]))
>- (`?M w:β. ¬satis M w f1 /\ satis M w f2` suffices_by metis_tac[] >>
   qexists_tac `<| frame := <| world := {b};
                           rel := λn1 n2. (n1 = b /\ n2 = b) |>;
                   valt := λa w. (σ a) |>` >>
   qabbrev_tac `M = <| frame := <| world := {b};
                           rel := λn1 n2. (n1 = b /\ n2 = b) |>;
                   valt := λa w. (σ a) |>` >>
   qexists_tac `b` >> rw[]
   >- (`¬satis M b f1` suffices_by metis_tac[] >>
      `b IN M.frame.world` by fs[Abbr`M`] >>
      `¬peval (λa. b ∈ M.valt a) f1` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])
   >- (`b IN M.frame.world` by fs[Abbr`M`] >>
      `(peval (λa. b ∈ M.valt a) f2)` suffices_by metis_tac[peval_satis] >>
      rw[IN_DEF,Abbr`M`] >> `(λa. σ a) = σ` by rw[FUN_EQ_THM] >> fs[])));

val partition_to_peval_well_defined = store_thm(
"partition_to_peval_well_defined",
``!f1 f2. (propform f1 /\ propform f2 /\ equiv0 μ f1 f2) ==> ((λf s. peval s f) f1) = ((λf s. peval s f) f2)``,
rw[equiv0_def] >> simp[FUN_EQ_THM] >> metis_tac[peval_equiv0]);



val IMAGE_peval_singlton_strengthen = store_thm(
"IMAGE_peval_singlton_strengthen",
``!x form. x IN {f | propform f /\ ∀a. (VAR a) IN (subforms f) ⇒ a ∈ s}//e /\ form IN x ==>
IMAGE (λf. {σ | peval σ f} ∩ POW s) x = {{σ | (peval σ form)} INTER (POW s)}``,
rw[partition_def] >> rw[IMAGE_DEF] >>
`!f. propform f /\ (equiv0 μ x' f) ==> ((λs. peval s f) = (λs. peval s form))` by
(rw[] >> fs[] >> `equiv0 μ f form` by metis_tac[equiv0_def] >> simp[FUN_EQ_THM] >> metis_tac[partition_to_peval_well_defined]) >>
simp[Once EXTENSION] >> rw[] >> eq_tac >> rw[]
>- fs[EXTENSION]
>- (qexists_tac `form` >> fs[EXTENSION]));

val INTER_EQ = store_thm(
  "INTER_EQ",
  ``!a b c. a ∩ c = b ∩ c ==>
  (!x. x IN c ==> (x IN a <=> x IN b))``,
  rw[EQ_IMP_THM]
  >- (`x IN (a ∩ c)` by fs[INTER_DEF] >>
     `x IN (b ∩ c)` by (fs[EXTENSION] >> metis_tac[]) >>
     `x IN b` by fs[INTER_DEF])
  >- (`x IN (b ∩ c)` by fs[INTER_DEF] >>
     `x IN (a ∩ c)` by (fs[EXTENSION] >> metis_tac[]) >>
     fs[INTER_DEF]));

val INJ_peval_partition_strengthen = store_thm(
  "INJ_peval_partition_strengthen",
  ``INJ
  (\eqc. ((IMAGE (λf. {s| peval s f} INTER (POW s)) eqc)))
  {f | propform f /\ ∀a. (VAR a) IN (subforms f) ⇒ a ∈ s}//e
  (POW (POW (POW s)))``,
  rw[INJ_DEF] >> fs[partition_def] >> simp[EXTENSION] >> fs[]
  >- (rw[IMAGE_DEF] >> fs[POW_DEF,SUBSET_DEF] >> rw[] >> fs[INTER_DEF])
  >- (rw[EQ_IMP_THM] >>
      `equiv0 μ x x'` suffices_by metis_tac[equiv0_SYM,equiv0_TRANS] >>
        `{y |
              (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧
              equiv0 μ x y} IN
         {f | propform f /\ ∀a. (VAR a) IN (subforms f) ⇒ a ∈ s}//e`
            by (rw[partition_def] >> qexists_tac `x` >> rw[]) >>
        `x IN {y |
         (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y}` by fs[equiv0_REFL] >>
        `{y |
              (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧
              equiv0 μ x' y} IN
         {f | propform f /\ ∀a. (VAR a) IN (subforms f) ⇒ a ∈ s}//e`
            by (rw[partition_def] >> qexists_tac `x'` >> rw[]) >>
        `x' IN {y |
         (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x' y}` by fs[equiv0_REFL] >>
        `IMAGE (λf. {σ | peval σ f} ∩ POW s) {y | (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y} =
     {{σ | peval σ x} ∩ POW s}` by metis_tac[IMAGE_peval_singlton_strengthen] >>
        `IMAGE (λf. {σ | peval σ f} ∩ POW s) {y | (propform y ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x' y} =
     {{σ | peval σ x'} ∩ POW s}` by metis_tac[IMAGE_peval_singlton_strengthen] >> fs[] >>
        `!σ. σ IN (POW s) ==> (σ IN {s | peval s x} <=> σ IN {s | peval s x'})` by metis_tac[INTER_EQ] >> fs[] >> rw[equiv0_def] >>
        irule equiv0_peval_strengthen >- (qexists_tac `s` >> rw[])
                                     >> rw[] >> qexists_tac `s` >> rw[]));




val DEG_IBC_strengthen = store_thm(
  "DEG_IBC_strengthen",
  ``∀x.
   DEG x ≤ n + 1 ∧ (∀a. (VAR a) IN subforms x ⇒ a ∈ s) ⇔
   IBC x
     ({VAR v | v ∈ s} ∪
      {◇ psi | DEG psi ≤ n ∧ ∀a. (VAR a) IN subforms psi ⇒ a ∈ s})``,
Induct_on `x` >> rw[DEG_def]
>- (simp[SimpRHS,Once IBC_cases] >> rw[subforms_def])
>- (`IBC (DISJ x x')
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}) ==>
   IBC x
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s})`
       by rw[Once IBC_cases] >>
   `(∀a. VAR a ∈ subforms (DISJ x x') ⇒ a ∈ s) ==>
   (∀a. VAR a ∈ subforms x ⇒ a ∈ s)` by rw[subforms_def] >>
   `IBC (DISJ x x')
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}) ==>
   IBC x'
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s})`
       by rw[Once IBC_cases] >>
   `(∀a. VAR a ∈ subforms (DISJ x x') ⇒ a ∈ s) ==>
   (∀a. VAR a ∈ subforms x' ⇒ a ∈ s)` by rw[subforms_def] >>
   rw[EQ_IMP_THM]
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- (`(∀a. VAR a ∈ subforms x' ⇒ a ∈ s)` by metis_tac[] >>
      `(∀a. VAR a ∈ subforms x ⇒ a ∈ s)` by metis_tac[] >>
      fs[subforms_def]))
>- fs[subforms_def,Once IBC_cases]
>- (`IBC (¬x)
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}) ==>
   IBC x
  ({VAR v | v ∈ s} ∪
   {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s})`
       by rw[Once IBC_cases] >>
   `(∀a. VAR a ∈ subforms (¬x) ⇒ a ∈ s) ==>
   (∀a. VAR a ∈ subforms x ⇒ a ∈ s)` by rw[subforms_def] >>
   rw[EQ_IMP_THM]
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- fs[subforms_def])
>- fs[Once IBC_cases,subforms_def]);
 

val IBC_EMPTY_lemma = store_thm(
  "IBC_EMPTY_lemma",
  ``∀f s. IBC f s ==> s = {} ==> equiv0 μ f TRUE \/ equiv0 μ f FALSE``,
  Induct_on `IBC` >> rw[] >> fs[equiv0_def,satis_def,TRUE_def]);


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
  ``!fs. FINITE fs ==> FINITE (partition (equiv0 μ) {f | IBC f fs})``,
  rw[] >> Cases_on `fs = {}`
  >- (fs[partition_def] >>
     `{t | ∃x. IBC x ∅ ∧ t = {y | IBC y ∅ ∧ equiv0 μ x y}} = {{y | IBC y ∅ ∧ equiv0 μ TRUE y};{y | IBC y ∅ ∧ equiv0 μ FALSE y}}` by (fs[EXTENSION] >> rw[] >> eq_tac >> rw[]
     >- (`equiv0 μ x' TRUE \/ equiv0 μ x' FALSE` by metis_tac[IBC_EMPTY_lemma]
        >> fs[equiv0_def,satis_def,TRUE_def])
     >- (qexists_tac `TRUE` >> rw[] >> rw[Once IBC_cases,TRUE_def] >> metis_tac[IBC_cases])
     >- (qexists_tac `FALSE` >> rw[] >> rw[Once IBC_cases,TRUE_def])) >>
     fs[]) >>
  qabbrev_tac `ff = \s.{d | DNF_OF d fs /\ (!f. f IN s ==> equiv0 μ d f)}` >>
  `FINITE {f | DNF_OF f fs}` by metis_tac[FINITE_DNF] >>
  `INJ ff ({f | IBC f fs}//e) (POW {f | DNF_OF f fs})` suffices_by metis_tac[FINITE_POW,FINITE_INJ] >>
  simp[INJ_DEF,IN_POW] >> rw[]
  >- simp[Abbr`ff`,SUBSET_DEF] >>
  SPOSE_NOT_THEN ASSUME_TAC >>
  `DISJOINT x y` by metis_tac[partition_elements_disjoint,equiv0_equiv_on]>>
  `(∀f1 f2. f1 ∈ x /\ f2 ∈ x ==> equiv0 μ f1 f2) /\
   (∀f1 f2. f1 ∈ y /\ f2 ∈ y ==> equiv0 μ f1 f2)`
     by metis_tac [partition_elements_interrelate,equiv0_equiv_on] >>
  fs[Abbr`ff`] >>
  `(equiv0 μ) equiv_on {f | IBC f fs}` by metis_tac[equiv0_equiv_on] >>
  `∀f1 f2. f1 ∈ x /\ f2 ∈ y ==> ¬equiv0 μ f1 f2` by metis_tac[equiv_on_partition_NOT_R] >>
  qpat_x_assum `GSPEC _ = GSPEC _` mp_tac >> simp[EXTENSION] >>
  `x <> {}` by metis_tac[EMPTY_NOT_IN_partition,equiv0_equiv_on] >>
  `?fx. fx IN x` by metis_tac[MEMBER_NOT_EMPTY] >>
  `x ⊆ {f | IBC f fs}` by metis_tac[partition_SUBSET] >>
  `IBC fx fs` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  `∃d. DNF_OF d fs /\ equiv0 μ fx d` by metis_tac[IBC_DNF_EXISTS] >>
  qexists_tac`d` >> simp[] >>
  `∀f. f ∈ x ==> equiv0 μ d f` by metis_tac[equiv0_SYM, equiv0_TRANS] >> simp[]>>
  `y <> {}` by metis_tac[EMPTY_NOT_IN_partition,equiv0_equiv_on] >>
  `∃fy. fy ∈ y` by metis_tac[MEMBER_NOT_EMPTY] >>
  qexists_tac `fy` >> simp[] >> metis_tac[equiv0_SYM, equiv0_TRANS]);


val IBC_partition_equiv0 = store_thm(
  "IBC_partition_equiv0",
  ``!f fs. IBC f fs ==> fs <> {} ==>
         ?p. IBC p (IMAGE CHOICE (partition (equiv0 μ) fs)) /\ equiv0 μ f p``,
Induct_on `IBC` >> rw[]
>- (`∃p. IBC p (IMAGE CHOICE fs//e) ∧ equiv0 μ f p /\
   ∃p'. IBC p' (IMAGE CHOICE fs//e) ∧ equiv0 μ f' p'` by metis_tac[] >>
   qexists_tac `DISJ p p'` >> rw[]
   >- metis_tac[IBC_cases]
   >- fs[equiv0_def,satis_def])
>- (qexists_tac `FALSE` >> rw[Once IBC_cases])
>- (`∃p. IBC p (IMAGE CHOICE fs//e) ∧ equiv0 μ f p` by metis_tac[] >>
   qexists_tac `¬p` >> rw[Once IBC_cases] >> fs[equiv0_def,satis_def])
>- (fs[partition_def] >>
   qexists_tac `CHOICE {y | y IN fs /\ equiv0 μ f y}` >> rw[]
   >- (`(CHOICE {y | y ∈ fs ∧ equiv0 μ f y}) IN (IMAGE CHOICE {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 μ x y}})` by (fs[IMAGE_DEF,PULL_EXISTS] >> qexists_tac `f` >> rw[]) >> metis_tac[IBC_cases]) >>
   `{y | y ∈ fs ∧ equiv0 μ f y} <> {}` by (`f IN {y | y ∈ fs ∧ equiv0 μ f y}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
   `(CHOICE {y | y ∈ fs ∧ equiv0 μ f y}) IN {y | y ∈ fs ∧ equiv0 μ f y}` by metis_tac[CHOICE_DEF] >> fs[]));

val IBC_SUBSET = store_thm(
    "IBC_SUBSET",
    ``!f fs. IBC f fs ==> !gs. fs SUBSET gs ==> IBC f gs``,
    Induct_on `IBC` >> rw[]
    >> metis_tac[SUBSET_DEF,IBC_cases]);


Theorem FINITE_FINITE_IBC:
  !fs. fs <> {} ==> FINITE (partition (equiv0 μ) fs) ==>
       FINITE (partition (equiv0 μ) {f | IBC f fs})
Proof
  rw[] >>
  `FINITE (IMAGE CHOICE fs//e)` by metis_tac[IMAGE_FINITE] >>
  `FINITE {f | IBC f (IMAGE CHOICE fs//e)}//e` by metis_tac[IBC_FINITE] >>
  `fs//e <> {}` by metis_tac[partition_eq_EMPTY] >>
  `?ff. SURJ ff ({f | IBC f (IMAGE CHOICE fs//e)}//e) ({f | IBC f fs}//e)`
    by (fs[partition_def] >>
        qabbrev_tac `ff = \s. {y | IBC y fs /\ !f. f IN s ==> equiv0 μ y f}` >>
        rw[SURJ_DEF] >>
        qexists_tac `ff` >> rw[]
        >- (rename [‘IBC xx _’] >> fs[partition_def,Abbr`ff`] >>
            qexists_tac `xx` >> rw[]
            >- (`(IMAGE CHOICE
                        {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 μ x y}})
                  SUBSET fs`
                 by (rw[IMAGE_DEF,SUBSET_DEF] >>
                     qmatch_abbrev_tac ‘CHOICE smallset ∈ bigset’ >>
                     `smallset <> {}`
                         by (simp[Abbr`smallset`, EXTENSION] >>
                             metis_tac[equiv0_REFL]) >>
                     ‘smallset ⊆ bigset’
                       suffices_by metis_tac[SUBSET_DEF, CHOICE_DEF] >>
                     simp[SUBSET_DEF, Abbr`smallset`, Abbr`bigset`]) >>
                metis_tac[IBC_SUBSET])
            >- (rw[EXTENSION,EQ_IMP_THM]
                >- (qabbrev_tac `
                      A = {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 μ x y}}` >>
                    qabbrev_tac `
                      B = {t | ∃x.
                                  x ∈ fs ∧
                                  ∀x''.
                                    (x'' ∈ t ⇒ x'' ∈ fs ∧ equiv0 μ x x'') ∧
                                    (x'' ∈ fs ∧ equiv0 μ x x'' ⇒ x'' ∈ t)}` >>
                    ‘A ⊆ B’
                      by (rw[SUBSET_DEF,Abbr‘A’, Abbr‘B’] >> simp[] >>
                          PROVE_TAC[]) >>
                    `(IMAGE CHOICE A) SUBSET (IMAGE CHOICE B)`
                      by metis_tac[IMAGE_SUBSET] >>
                    `IBC xx (IMAGE CHOICE B)` by metis_tac[IBC_SUBSET] >>
                    metis_tac[equiv0_REFL,equiv0_SYM,equiv0_TRANS])
                >> metis_tac[equiv0_SYM,equiv0_TRANS]))
        >- (fs[partition_def] >>
            qabbrev_tac `
              A = {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 μ x y}}` >>
            simp[PULL_EXISTS] >>
            FREEZE_THEN drule IBC_partition_equiv0 >>
            rw[] >> qexists_tac `p` >> rw[]
            >- fs[partition_def,Abbr`A`]
            >- (rw[Abbr`ff`,EXTENSION,EQ_IMP_THM]
                >- (fs[partition_def,Abbr`A`] >> `equiv0 μ x p` by fs[] >>
                    metis_tac[equiv0_SYM,equiv0_TRANS])
                >- metis_tac[equiv0_SYM,equiv0_TRANS]))) >>
  metis_tac[FINITE_SURJ]
QED

val NOT_equiv0_VAR_DIAM = store_thm(
    "NOT_equiv0_VAR_DIAM",
    ``!a f. ¬(equiv0 (μ:β itself) (VAR a) (DIAM f))``,
    rw[equiv0_def] >>
    `?M w:β. satis M w (VAR a) /\ ¬(satis M w (◇ f))` suffices_by metis_tac[] >>
    `univ(:'b) <> {}` by metis_tac[UNIV_NOT_EMPTY] >>
    `?b. b IN (univ(:'b))` by metis_tac[MEMBER_NOT_EMPTY] >>
    qexists_tac `<| frame := <| world := {b};
                           rel := λn1 n2. F |>;
                   valt := λe w. T|>` >> qexists_tac `b` >> rw[]
    >> rw[satis_def]);


val equiv0_DIAM_lemma = store_thm(
  "equiv0_DIAM_lemma",
  ``!f g μ:'a itself. INFINITE univ(:'a) ==> ¬(equiv0 μ f g) ==> ¬(equiv0 μ (DIAM f) (DIAM g))``,
  rw[EQ_equiv0_def] >>
  `∃f:'a -> 'a. (∀x y. f x = f y ⇒ x = y) ∧ ∃y. ∀x. f x ≠ y` by metis_tac[INFINITE_UNIV] >>
  `(satis M w f /\ ¬satis M w g) \/ (¬satis M w f /\ satis M w g)` by metis_tac[] (* 2 *)
  >- (qexists_tac `<| frame := <| world := y INSERT (IMAGE f' M.frame.world);
                                    rel := λn1 n2. (?m1 m2. m1 IN M.frame.world /\ m2 IN M.frame.world /\
                                           M.frame.rel m1 m2 /\ f' m1 = n1 /\ f' m2 = n2) \/
                                           (n1 = y /\ n2 = f' w) |>;
                       valt := \a b. (?c. f' c = b /\ M.valt a c) |>` >>
     qmatch_abbrev_tac `?w'. w' IN M'.frame.world /\ (satis M' w' (DIAM f) ⇎ satis M' w' (DIAM g))` >>
     qexists_tac `y` >> rw[] (* 2 *)
    >- fs[Abbr`M'`]
    >- (`satis M' y (DIAM f) /\ ¬satis M' y (DIAM g)` suffices_by metis_tac[] >> rw[satis_def] (* 3 *)
       >- fs[Abbr`M'`]
       >- (qexists_tac `f' w` >>
          `bounded_mor f' M M'`
              by (rw[bounded_mor_def] (* 4 *)
                  >- fs[Abbr`M'`]
                  >- (fs[Abbr`M'`] >> rw[satis_def] >> fs[IN_DEF] >> rw[EQ_IMP_THM] >> metis_tac[])
                  >- (fs[Abbr`M'`] >> metis_tac[])
                  >- (fs[Abbr`M'`] (* 4 *) >> metis_tac[])) >>
          `satis M w f <=> satis M' (f' w) f` by fs[prop_2_14] >>
          fs[Abbr`M'`])
       >- (`!v. M'.frame.rel y v /\ v IN M'.frame.world ==> ¬satis M' v g` suffices_by metis_tac[] >> rw[] >>
          `bounded_mor f' M M'`
              by (rw[bounded_mor_def] (* 4 *)
                  >- fs[Abbr`M'`]
                  >- (fs[Abbr`M'`] >> rw[satis_def] >> fs[IN_DEF] >> rw[EQ_IMP_THM] >> metis_tac[])
                  >- (fs[Abbr`M'`] >> metis_tac[])
                  >- (fs[Abbr`M'`] (* 4 *) >> metis_tac[])) >>
          fs[Abbr`M'`] (* 4 *)
          >- metis_tac[]
          >- metis_tac[]
          >- metis_tac[]
          >- (qmatch_abbrev_tac `¬satis M' (f' x) g` >> rw[] >>
             metis_tac[prop_2_14]))))
  >- (qexists_tac `<| frame := <| world := y INSERT (IMAGE f' M.frame.world);
                                    rel := λn1 n2. (?m1 m2. m1 IN M.frame.world /\ m2 IN M.frame.world /\
                                           M.frame.rel m1 m2 /\ f' m1 = n1 /\ f' m2 = n2) \/
                                           (n1 = y /\ n2 = f' w) |>;
                       valt := \a b. (?c. f' c = b /\ M.valt a c) |>` >>
     qmatch_abbrev_tac `?w'. w' IN M'.frame.world /\ (satis M' w' (DIAM f) ⇎ satis M' w' (DIAM g))` >>
     qexists_tac `y` >> rw[] (* 2 *)
    >- fs[Abbr`M'`]
    >- (`¬satis M' y (DIAM f) /\ satis M' y (DIAM g)` suffices_by metis_tac[] >> rw[satis_def] (* 3 *)
       >- (`!v. M'.frame.rel y v /\ v IN M'.frame.world ==> ¬satis M' v f` suffices_by metis_tac[] >> rw[] >>
          `bounded_mor f' M M'`
              by (rw[bounded_mor_def] (* 4 *)
                  >- fs[Abbr`M'`]
                  >- (fs[Abbr`M'`] >> rw[satis_def] >> fs[IN_DEF] >> rw[EQ_IMP_THM] >> metis_tac[])
                  >- (fs[Abbr`M'`] >> metis_tac[])
                  >- (fs[Abbr`M'`] (* 4 *) >> metis_tac[])) >>
          fs[Abbr`M'`] (* 4 *)
          >- metis_tac[]
          >- metis_tac[]
          >- metis_tac[]
          >- (qmatch_abbrev_tac `¬satis M' (f' x) f` >> rw[] >>
             metis_tac[prop_2_14]))
       >- fs[Abbr`M'`]
       >- (qexists_tac `f' w` >>
          `bounded_mor f' M M'`
              by (rw[bounded_mor_def] (* 4 *)
                  >- fs[Abbr`M'`]
                  >- (fs[Abbr`M'`] >> rw[satis_def] >> fs[IN_DEF] >> rw[EQ_IMP_THM] >> metis_tac[])
                  >- (fs[Abbr`M'`] >> metis_tac[])
                  >- (fs[Abbr`M'`] (* 4 *) >> metis_tac[])) >>
          `satis M w g <=> satis M' (f' w) g` by fs[prop_2_14] >>
          fs[Abbr`M'`]))));




val equiv0_DIAM = store_thm(
    "equiv0_DIAM",
    ``!f g μ. INFINITE univ(:'b) ==> (equiv0 (μ:'b itself) (DIAM f) (DIAM g) <=> equiv0 μ f g)``,
    rw[EQ_IMP_THM]
    >- (SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[equiv0_DIAM_lemma])
    >- fs[equiv0_def,satis_def]);



Theorem prop_2_29_strengthen:
  !s. FINITE s /\ INFINITE univ(:'b) ==>
      !n. FINITE (partition (equiv0 (μ:'b itself))
                            { f| DEG f <= n /\
                                 (!a. (VAR a) IN (subforms f) ==> a IN s)})
Proof
gen_tac >> strip_tac >>
Induct_on `n`
>- (`{f | DEG f ≤ 0 ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s} =
   {f | propform f ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` by (simp[EXTENSION] >> metis_tac[DEG_0_propform]) >> fs[] >>
   `FINITE (POW (POW (POW s)))` by metis_tac[FINITE_POW] >>
   metis_tac[INJ_peval_partition_strengthen,FINITE_INJ])
>> (* step case *)
   `SUC n = n + 1` by fs[] >> rw[] >>
   `{f | DEG f ≤ n + 1 ∧ ∀a. (VAR a) IN subforms f ⇒ a ∈ s} = {phi | IBC phi ({VAR v | v IN s} UNION {DIAM psi | DEG psi <= n /\ ∀a. (VAR a) IN subforms psi ⇒ a ∈ s})}`
       by (fs[EXTENSION] >> rw[EQ_IMP_THM] (* 3 *)
           >> metis_tac[DEG_IBC_strengthen]) >> simp[] >>
   Cases_on `{VAR v | v ∈ s} ∪
      {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s} = {}`
   (* empty case *)
   >- (fs[] >> fs[partition_def] >>
      `{t | ∃x. IBC x ∅ ∧ t = {y | IBC y ∅ ∧ equiv0 μ x y}} = {{f | IBC f {} /\ equiv0 μ f TRUE};{f | IBC f {} /\ equiv0 μ f FALSE}}` by
      (simp[Once EXTENSION] >> rw[] >> eq_tac >> rw[] (* 3 *)
      >- (FREEZE_THEN drule (IBC_EMPTY_lemma|> INST_TYPE [alpha |-> ``:'b``]) >> rw[]
         >- (`{y | IBC y ∅ ∧ equiv0 μ x' y} = {f | IBC f ∅ ∧ equiv0 μ f TRUE}` suffices_by metis_tac[] >>
            rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv0_SYM,equiv0_TRANS])
         >- (`{y | IBC y ∅ ∧ equiv0 μ x' y} = {f | IBC f ∅ ∧ equiv0 μ f FALSE}` suffices_by metis_tac[] >>
            rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv0_SYM,equiv0_TRANS]))
      >- (qexists_tac `TRUE` >> rw[]
         >- (rw[Once IBC_cases] >>
            `∃f. TRUE = ¬f ∧ IBC f ∅` suffices_by metis_tac[] >> qexists_tac `FALSE` >> metis_tac[IBC_cases,TRUE_def])
         >- (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv0_SYM]))
      >- (qexists_tac `FALSE` >> rw[]
         >- rw[Once IBC_cases]
         >- (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv0_SYM]))) >> fs[])
   (* nonempty case *)
   >- (irule (FINITE_FINITE_IBC |> INST_TYPE [alpha |-> ``:'b``]) (* 2 *)
      >- (`({VAR v | v ∈ s} ∪ {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s})//E μ =
          {VAR v | v ∈ s}//E μ ∪ {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}//E μ`
             by (irule (equiv_on_disjoint_partition |> INST_TYPE [alpha |-> ``:'b``])
                >- (rw[] >> metis_tac[NOT_equiv0_VAR_DIAM])
                >- metis_tac[equiv0_equiv_on]
                >- metis_tac[equiv0_equiv_on])
                >> rw[] (* 2 *)
          >-  (`FINITE {VAR v | v IN s}` suffices_by metis_tac[FINITE_partition] >>
               `SURJ VAR s {VAR v | v IN s}` suffices_by metis_tac[FINITE_SURJ] >> rw[SURJ_DEF])
          >- (qabbrev_tac `A = {psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}//E μ` >>
               qabbrev_tac `B = {◇ psi | DEG psi ≤ n ∧ ∀a. VAR a ∈ subforms psi ⇒ a ∈ s}//E μ` >>
               `?ff. SURJ ff A B` suffices_by metis_tac[FINITE_SURJ] >>
               qexists_tac `\s. {DIAM t | t IN s}` >> rw[SURJ_DEF] (* 2 *)
               >- (fs[Abbr`B`] >> rw[Once EXTENSION,partition_def] >> fs[PULL_EXISTS] >> fs[Abbr`A`,partition_def] >>
                  qexists_tac `x` >> rw[] >> eq_tac >> rw[] (* 4 *) >> metis_tac[equiv0_DIAM])
               >- (fs[Abbr`A`,Abbr`B`] (* 2 *)
                  >> (fs[partition_def] >> fs[PULL_EXISTS] >>
                     qexists_tac `psi` >> fs[] >> rw[EXTENSION] >> eq_tac >> rw[] (* 2 *) >> metis_tac[equiv0_DIAM]))))
       >- rw[])
QED


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
``!M M' n w w'. (?f. nbisim M M' f n w w') ==> (!(phi:form). DEG phi <= n ==> (satis M w phi <=> satis M' w' phi))``,
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


val BIGCONJ_EXISTS_2_2 = store_thm(
"BIGCONJ_EXISTS_2",
``∀s.
     FINITE s ⇒
     ?ff.
     ∀w M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)``,
Induct_on `FINITE s` >> rpt strip_tac
>- (qexists_tac `TRUE` >> rw[] >> metis_tac[satis_def,TRUE_def])
>- (qexists_tac `AND ff e` >> rw[] >> eq_tac
   >- (rpt strip_tac >- metis_tac[satis_AND]
                     >- (`satis M w ff` by metis_tac[satis_AND] >> metis_tac[]))
   >- (rw[] >> `e = e ==> satis M w e` by metis_tac[] >> `e = e` by metis_tac[] >>
      `satis M w e` by metis_tac[] >>
      `!f. f IN s ==> satis M w f` by metis_tac[] >>
      `satis M w ff` by metis_tac[] >>
      metis_tac[satis_AND])));



val BIGCONJ_EXISTS_DEG = store_thm(
  "BIGCONJ_EXISTS_DEG",
  ``∀s.
     FINITE s ⇒
     !n. (!f:form. f IN s ==> DEG f <= n) ==>
     ?ff. DEG ff <= n /\
     (∀w:'b M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)) /\
     (∀w:'c M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f))``,
  Induct_on `FINITE` >> rw[]
  >- (qexists_tac `TRUE` >> rw[TRUE_def,satis_def,DEG_def])
  >- (`∀f. f ∈ s ⇒ DEG f ≤ n` by metis_tac[] >>
     first_x_assum drule >> rw[] >>
     qexists_tac `AND e ff` >> rw[DEG_def,satis_def,AND_def] >> eq_tac >> rw[]
     >- rw[]
     >> metis_tac[]));


val equiv0_INFINITE_UNIV = store_thm(
  "equiv0_INFINITE_UNIV",
  ``INFINITE univ(:'a) ==> (equiv0 (:num) f1 f2 <=> equiv0 (:'a) f1 f2)``,
  `INFINITE 𝕌(:α) ⇒ (¬equiv0 (:num) f1 f2 ⇔ ¬equiv0 (:α) f1 f2)` suffices_by metis_tac[] >>
  strip_tac >> eq_tac
  >- (rw[] >>
     `?M w:num. (satis M w f1 /\ ¬satis M w f2) \/ (¬satis M w f1 /\ satis M w f2)` by metis_tac[equiv0_def] (* 2 *)
     >- (`satis M w (NOT f2)` by metis_tac[satis_def,satis_in_world] >>
        `satis M w (AND f1 (NOT f2))` by metis_tac[satis_AND] >>
        `∃f. INJ f 𝕌(:num) univ(:'a)` by metis_tac[infinite_num_inj] >>
        qabbrev_tac `N = <| frame := <| world := {f n| n IN M.frame.world};
                                          rel := (\a1 a2. ?n1 n2. n1 IN M.frame.world /\
                                                                  n2 IN M.frame.world /\
                                                                  f n1 = a1 /\ f n2 = a2 /\
                                                                  M.frame.rel n1 n2) |>;
                             valt := (\p a:'a. (?n. n IN M.frame.world /\ f n = a /\ M.valt p n)) |>` >>
        `bounded_mor f M N`
            by (rw[bounded_mor_def] (* 4 *)
               >- (fs[Abbr`N`] >>  qexists_tac `w'` >> rw[])
               >- (rw[satis_def] >> eq_tac >> rw[] >- (fs[Abbr`N`] >> qexists_tac `w'` >> rw[])
                                                   >- (fs[Abbr`N`] >> metis_tac[IN_DEF])
                                                   >- (fs[Abbr`N`] >>
                                                      `n' = w'` by fs[INJ_DEF] >> fs[IN_DEF]))
               >- (fs[Abbr`N`] >> map_every qexists_tac [`w'`,`v`] >> fs[])
               >- (fs[Abbr`N`] >> qexists_tac `n` >> rw[] >>
                  `n2 = n /\ n1 = w'` by fs[INJ_DEF] >> fs[])) >>
        `w IN M.frame.world` by metis_tac[satis_in_world] >>
        `satis N (f w) (AND f1 (NOT f2))` by metis_tac[prop_2_14] >>
        `satis N (f w) f1 /\ satis N (f w) (NOT f2)` by metis_tac[satis_AND] >>
        `¬satis N (f w) f2` by metis_tac[satis_def] >>
        rw[equiv0_def] >> map_every qexists_tac [`N`,`f w`] >> metis_tac[])
     >- (`satis M w (NOT f1)` by metis_tac[satis_def,satis_in_world] >>
        `satis M w (AND f2 (NOT f1))` by metis_tac[satis_AND] >>
        `∃f. INJ f 𝕌(:num) univ(:'a)` by metis_tac[infinite_num_inj] >>
        qabbrev_tac `N = <| frame := <| world := {f n| n IN M.frame.world};
                                          rel := (\a1 a2. ?n1 n2. n1 IN M.frame.world /\
                                                                  n2 IN M.frame.world /\
                                                                  f n1 = a1 /\ f n2 = a2 /\
                                                                  M.frame.rel n1 n2) |>;
                             valt := (\p a:'a. (?n. n IN M.frame.world /\ f n = a /\ M.valt p n)) |>` >>
        `bounded_mor f M N`
            by (rw[bounded_mor_def] (* 4 *)
               >- (fs[Abbr`N`] >>  qexists_tac `w'` >> rw[])
               >- (rw[satis_def] >> eq_tac >> rw[] >- (fs[Abbr`N`] >> qexists_tac `w'` >> rw[])
                                                   >- (fs[Abbr`N`] >> metis_tac[IN_DEF])
                                                   >- (fs[Abbr`N`] >>
                                                      `n' = w'` by fs[INJ_DEF] >> fs[IN_DEF]))
               >- (fs[Abbr`N`] >> map_every qexists_tac [`w'`,`v`] >> fs[])
               >- (fs[Abbr`N`] >> qexists_tac `n` >> rw[] >>
                  `n2 = n /\ n1 = w'` by fs[INJ_DEF] >> fs[]))>>
        `w IN M.frame.world` by metis_tac[satis_in_world] >>
        `satis N (f w) (AND f2 (NOT f1))` by metis_tac[prop_2_14] >>
        `satis N (f w) f2 /\ satis N (f w) (NOT f1)` by metis_tac[satis_AND] >>
        `¬satis N (f w) f1` by metis_tac[satis_def] >>
        rw[equiv0_def] >> map_every qexists_tac [`N`,`f w`] >> metis_tac[]))
  >- (rw[] >>
     `?M w:'a. (satis M w f1 /\ ¬satis M w f2) \/ (¬satis M w f1 /\ satis M w f2)` by metis_tac[equiv0_def] (* 2 *)
     >- (`satis M w (NOT f2)` by metis_tac[satis_def,satis_in_world] >>
        `satis M w (AND f1 (NOT f2))` by metis_tac[satis_AND] >>
        `?M' w':'a. w' IN M'.frame.world /\ satis M' w' (AND f1 (NOT f2)) /\ FINITE M'.frame.world`
            by metis_tac[thm_2_41] >>
        `∃f. INJ f M'.frame.world univ(:num)`
            by metis_tac[finite_countable,countable_def] >>
        qabbrev_tac `N = <| frame := <| world := {f a| a IN M'.frame.world};
                                          rel := (\n1 n2. ?a1 a2. a1 IN M'.frame.world /\
                                                                  a2 IN M'.frame.world /\
                                                                  f a1 = n1 /\ f a2 = n2 /\
                                                                  M'.frame.rel a1 a2) |>;
                             valt := (\p n:num. (?a. a IN M'.frame.world /\ f a = n /\ M'.valt p a)) |>` >>
        `bounded_mor f M' N`
            by (rw[bounded_mor_def] (* 4 *)
               >- (fs[Abbr`N`] >> qexists_tac `w''` >> rw[])
               >- (rw[satis_def] >> eq_tac >> rw[] >- (fs[Abbr`N`] >> qexists_tac `w''` >> rw[])
                                                   >- (fs[Abbr`N`] >> qexists_tac `w''` >> fs[IN_DEF])
                                                   >- (fs[Abbr`N`] >> `a'' = w''` by metis_tac[INJ_DEF] >> metis_tac[IN_DEF]))
               >- (fs[Abbr`N`] >> map_every qexists_tac [`w''`,`v`] >> fs[])
               >- (fs[Abbr`N`] >> qexists_tac `a` >> rw[] >>
                  `a2 = a /\ a1 = w''` by fs[INJ_DEF] >> fs[])) >>
        `satis N (f w') (AND f1 (NOT f2))` by metis_tac[prop_2_14] >>
        `satis N (f w') f1 /\ satis N (f w') (NOT f2)` by metis_tac[satis_AND] >>
        `¬satis N (f w') f2` by metis_tac[satis_def] >>
        rw[equiv0_def] >> map_every qexists_tac [`N`,`f w'`] >> metis_tac[])
     >- (`satis M w (NOT f1)` by metis_tac[satis_def,satis_in_world] >>
        `satis M w (AND f2 (NOT f1))` by metis_tac[satis_AND] >>
        `?M' w':'a. w' IN M'.frame.world /\ satis M' w' (AND f2 (NOT f1)) /\ FINITE M'.frame.world`
            by metis_tac[thm_2_41] >>
        `∃f. INJ f M'.frame.world univ(:num)`
            by metis_tac[finite_countable,countable_def] >>
        qabbrev_tac `N = <| frame := <| world := {f a| a IN M'.frame.world};
                                          rel := (\n1 n2. ?a1 a2. a1 IN M'.frame.world /\
                                                                  a2 IN M'.frame.world /\
                                                                  f a1 = n1 /\ f a2 = n2 /\
                                                                  M'.frame.rel a1 a2) |>;
                             valt := (\p n:num. (?a. a IN M'.frame.world /\ f a = n /\ M'.valt p a)) |>` >>
        `bounded_mor f M' N`
            by (rw[bounded_mor_def] (* 4 *)
               >- (fs[Abbr`N`] >> qexists_tac `w''` >> rw[])
               >- (rw[satis_def] >> eq_tac >> rw[] >- (fs[Abbr`N`] >> qexists_tac `w''` >> rw[])
                                                   >- (fs[Abbr`N`] >> qexists_tac `w''` >> fs[IN_DEF])
                                                   >- (fs[Abbr`N`] >> `a'' = w''` by metis_tac[INJ_DEF] >> metis_tac[IN_DEF]))
               >- (fs[Abbr`N`] >> map_every qexists_tac [`w''`,`v`] >> fs[])
               >- (fs[Abbr`N`] >> qexists_tac `a` >> rw[] >>
                  `a2 = a /\ a1 = w''` by fs[INJ_DEF] >> fs[])) >>
        `satis N (f w') (AND f2 (NOT f1))` by metis_tac[prop_2_14] >>
        `satis N (f w') f2 /\ satis N (f w') (NOT f1)` by metis_tac[satis_AND] >>
        `¬satis N (f w') f1` by metis_tac[satis_def] >>
        rw[equiv0_def] >> map_every qexists_tac [`N`,`f w'`] >> metis_tac[])));

val equiv0_equal_for_INFINITE_UNIV = store_thm(
  "equiv0_equal_for_INFINITE_UNIV",
  ``INFINITE univ(:'a) /\ INFINITE univ(:'b)
    ==> (equiv0 (:'a) = equiv0 (:'b))``,
  simp[FUN_EQ_THM] >> rw[] >>
  `(equiv0 (:num) x x' ⇔ equiv0 (:α) x x')` by metis_tac[equiv0_INFINITE_UNIV] >>
  `(equiv0 (:num) x x' ⇔ equiv0 (:'b) x x')` by metis_tac[equiv0_INFINITE_UNIV] >>
  metis_tac[]);
(*
val prop_2_31_half2 = store_thm(
  "prop_2_31_half2",
  ``!M M' n w:'b w':'c.
  (INFINITE univ(:'b) /\ INFINITE univ(:'c) /\ FINITE univ (:'a) /\
  w IN M.frame.world /\ w' IN M'.frame.world)
  ==> (!(phi: form). DEG phi <= n ==> (satis M w phi <=> satis M' w' phi))
      ==> ?f. nbisim M M' f n w w'``,
  rpt strip_tac >>
  rw[nbisim_def] >>
  qexists_tac `λn n1 n2. (!(phi: form). DEG phi <= n ==> (satis M n1 phi <=> satis M' n2 phi))` >> rw[] >>
  `equiv0 (:'b) = equiv0 (:'c)` by metis_tac[equiv0_equal_for_INFINITE_UNIV]
  >- metis_tac[DEG_def]
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
     `∀u'.
          u' ∈ M'.frame.world /\ M'.frame.rel v' u' ==>
          (?form. DEG form <= i /\ satis M u form /\ ¬satis M' u' form)`
        by (rw[satis_def] >>
           `∃phi. DEG phi ≤ i ∧ (satis M u phi ⇎ satis M' u' phi)` by metis_tac[] >>
           Cases_on `satis M u phi` >- (qexists_tac `phi` >> metis_tac[])
                                    >- (qexists_tac `NOT phi` >> rw[]
                                                                >- metis_tac[DEG_def]
                                                                >> metis_tac[satis_def])) >>

    qabbrev_tac `
      s = {f | DEG f <= i /\ ?u'. u' IN M'.frame.world /\
               M'.frame.rel v' u' /\ satis M u f /\ ¬satis M' u' f}` >>
   `s ⊆ {f| DEG f <= i}` by (fs[Abbr`s`,SUBSET_DEF]) >>
   `(equiv0 (μ:'c itself)) equiv_on {f | DEG f ≤ i}` by metis_tac[equiv0_equiv_on] >>
   `FINITE (partition (equiv0 μ) s)`
       by (`(equiv0 μ) equiv_on {f | DEG f ≤ i}` by metis_tac[equiv0_equiv_on] >>
          `equiv0 (:'c) = equiv0 (:'b)` by metis_tac[equiv0_equal_for_INFINITE_UNIV] >>
          metis_tac[prop_2_29,FINITE_partition_SUBSET]) >>
   `FINITE (IMAGE CHOICE (s//E μ))` by metis_tac[IMAGE_FINITE] >>
   `(equiv0 μ) equiv_on s` by metis_tac[equiv0_equiv_on] >>
   `!p. p IN (s//E μ) ==> p <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `!p. p IN (s//E μ) ==> (CHOICE p) IN p` by metis_tac[CHOICE_DEF] >>
   `!f. f IN (IMAGE CHOICE (s//E μ)) ==> DEG f <= i`
     by (dsimp[] >> rw[] >> `(CHOICE x) IN x` by metis_tac[] >>
         `x SUBSET s` by fs[partition_def,SUBSET_DEF] >>
         `(CHOICE x) IN s` by metis_tac[SUBSET_DEF, partition_def] >>
         fs[Abbr`s`]) >>
   imp_res_tac BIGCONJ_EXISTS_DEG >>
   `∀f. f ∈ IMAGE CHOICE (s//E μ) ⇒ satis M u f`
     by (rw[] >>
        `(CHOICE x) IN x` by metis_tac[] >>
        fs[partition_def,Abbr`s`] >> rw[] >> fs[]) >>
   `satis M u ff` by metis_tac[] >>
   `satis M v (DIAM ff)` by metis_tac[satis_def] >>
   `DEG (DIAM ff) <= i + 1` by fs[DEG_def] >>
   `¬satis M' v' (DIAM ff)` suffices_by metis_tac[] >>
   `∀u'. M'.frame.rel v' u' /\ u' ∈ M'.frame.world ==> ¬satis M' u' ff`
      suffices_by metis_tac[satis_def] >>
   rw[partition_def,PULL_EXISTS] >>
   `∃form. DEG form ≤ i ∧ satis M u form ∧ ¬satis M' u' form` by metis_tac[] >>
   `form IN s` by (fs[Abbr`s`] >> qexists_tac `u'` >> rw[]) >>
   rw[] >>
   `equiv0 μ form form` by metis_tac[equiv0_REFL] >> `form IN {y | y ∈ s ∧ equiv0 μ form y}` by fs[] >>
   `{y | y ∈ s ∧ equiv0 μ form y} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
   `(CHOICE {y | y ∈ s ∧ equiv0 μ form y}) IN {y | y ∈ s ∧ equiv0 μ form y}` by metis_tac[CHOICE_DEF] >>
   fs[] >>
   `¬satis M' u' (CHOICE {y | y ∈ s ∧ equiv0 μ form y})` by metis_tac[equiv0_def] >>
   `{y | y ∈ s ∧ equiv0 μ form y} IN (s//E μ)`
       by (rw[partition_def] >> qexists_tac `form` >> rw[]) >> metis_tac[])
>- (SPOSE_NOT_THEN ASSUME_TAC >>
     `∀u.
          u ∈ M.frame.world /\ M.frame.rel v u ==>
          (?form. DEG form <= i /\ satis M' u' form /\ ¬satis M u form)`
        by (rw[satis_def] >>
           `∃phi. DEG phi ≤ i ∧ (satis M' u' phi ⇎ satis M u phi)` by metis_tac[] >>
           Cases_on `satis M' u' phi` >- (qexists_tac `phi` >> metis_tac[])
                                    >- (qexists_tac `NOT phi` >> rw[]
                                                                >- metis_tac[DEG_def]
                                                                >> metis_tac[satis_def])) >>
   qabbrev_tac `s = {f | DEG f <= i /\ ?u. u IN M.frame.world /\
               M.frame.rel v u /\ satis M' u' f /\ ¬satis M u f}` >>
   `s ⊆ {f| DEG f <= i}` by (fs[Abbr`s`,SUBSET_DEF]) >>
   `(equiv0 (μ:'b itself)) equiv_on {f | DEG f ≤ i}` by metis_tac[equiv0_equiv_on] >>
   `FINITE (partition (equiv0 μ) s)`
       by (`(equiv0 μ) equiv_on {f | DEG f ≤ i}` by metis_tac[equiv0_equiv_on] >>
          `equiv0 (:'c) = equiv0 (:'b)` by metis_tac[equiv0_equal_for_INFINITE_UNIV] >>
          metis_tac[prop_2_29,FINITE_partition_SUBSET]) >>
   `FINITE (IMAGE CHOICE (s//E μ))` by metis_tac[IMAGE_FINITE] >>
   `(equiv0 μ) equiv_on s` by metis_tac[equiv0_equiv_on] >>
   `!p. p IN (s//E μ) ==> p <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
   `!p. p IN (s//E μ) ==> (CHOICE p) IN p` by metis_tac[CHOICE_DEF] >>
   `!f. f IN (IMAGE CHOICE (s//E μ)) ==> DEG f <= i`
     by (dsimp[] >> rw[] >> `(CHOICE x) IN x` by metis_tac[] >>
         `x SUBSET s` by fs[partition_def,SUBSET_DEF] >>
         `(CHOICE x) IN s` by metis_tac[SUBSET_DEF, partition_def] >>
         fs[Abbr`s`]) >>
   imp_res_tac BIGCONJ_EXISTS_DEG >>
   `∀f. f ∈ IMAGE CHOICE (s//E μ) ⇒ satis M' u' f`
     by (rw[] >>
        `(CHOICE x) IN x` by metis_tac[] >>
        fs[partition_def,Abbr`s`] >> rw[] >> fs[]) >>
   `satis M' u' ff` by metis_tac[] >>
   `satis M' v' (DIAM ff)` by metis_tac[satis_def] >>
   `DEG (DIAM ff) <= i + 1` by fs[DEG_def] >>
   `¬satis M v (DIAM ff)` suffices_by metis_tac[] >>
   `∀u. M.frame.rel v u /\ u ∈ M.frame.world ==> ¬satis M u ff`
      suffices_by metis_tac[satis_def] >>
   rw[partition_def,PULL_EXISTS] >>
   `∃form. DEG form ≤ i ∧ satis M' u' form ∧ ¬satis M u form` by metis_tac[] >>
   `form IN s` by (fs[Abbr`s`] >> qexists_tac `u` >> rw[]) >>
   rw[] >>
   `equiv0 μ form form` by metis_tac[equiv0_REFL] >> `form IN {y | y ∈ s ∧ equiv0 μ form y}` by fs[] >>
   `{y | y ∈ s ∧ equiv0 μ form y} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
   `(CHOICE {y | y ∈ s ∧ equiv0 μ form y}) IN {y | y ∈ s ∧ equiv0 μ form y}` by metis_tac[CHOICE_DEF] >>
   fs[] >>
   `¬satis M u (CHOICE {y | y ∈ s ∧ equiv0 μ form y})` by metis_tac[equiv0_def] >>
   `{y | y ∈ s ∧ equiv0 μ form y} IN (s//E μ)`
       by (rw[partition_def] >> qexists_tac `form` >> rw[]) >> metis_tac[]));
*)


val (heightLE_rules, heightLE_ind, heightLE_cases) = Hol_reln`
  (!n. heightLE (M:'b model) x (M':'b model) x n) /\
  (!v. v IN M.frame.world /\ (?w. w IN M.frame.world /\ M.frame.rel w v /\ heightLE M x M' w n) ==>
       heightLE M x M' v (n + 1))
`;


val height_def = Define`height M x M' w = MIN_SET {n | heightLE M x M' w n}`;

val model_height_def = Define`
model_height (M:'b model) x (M':'b model) = MAX_SET {n | ?w. w IN M.frame.world /\ height M x M' w = n}`;


val hrestriction_def = Define`
hrestriction M x M' n =
  <| frame := <| world := {w | w IN M.frame.world /\ height M x M' w <= n};
                 rel := λn1 n2. M.frame.rel n1 n2 |>;
     valt := λphi n. M.valt phi n |>`;

val heightLE_rel = store_thm(
  "heightLE_rel",
  ``!w n. heightLE M x M' w n ==> w IN M.frame.world /\ rooted_model M x M' ==> (!w'. M.frame.rel w w' /\ w' IN M.frame.world ==> heightLE M x M' w' (n + 1))``,
  Induct_on `heightLE` >> rw[]
  >- (rw[Once heightLE_cases] >>
     `∃w. w ∈ M.frame.world ∧ M.frame.rel w w' ∧ heightLE M x M' w n` suffices_by metis_tac[] >>
     qexists_tac `x` >> rw[] >> metis_tac[heightLE_cases])
  >- (`heightLE M x M' w (n + 1)` by metis_tac[] >>
     rw[Once heightLE_cases] >>
     `∃n'.
     n + 2 = n' + 1 ∧
     ∃w. w ∈ M.frame.world ∧ M.frame.rel w w'' ∧ heightLE M x M' w n'` suffices_by metis_tac[] >>
     qexists_tac `n + 1` >> rw[] >> qexists_tac `w` >> rw[]));

val heightLE_RTC = store_thm(
  "heightLE_RTC",
  ``!w n. heightLE M x M' w n ==>
  rooted_model M x M' ==> (RESTRICT M'.frame.rel M'.frame.world)^* x w``,
  Induct_on `heightLE` >> rw[] >>
  `(RESTRICT M'.frame.rel M'.frame.world)^* x w'` by metis_tac[] >>
  `RESTRICT M'.frame.rel M'.frame.world w' w` suffices_by metis_tac[RTC_CASES2] >>
  metis_tac[RESTRICT_def,rooted_model_def]);



val rooted_have_height = store_thm(
  "rooted_have_height",
  ``!x w. (RESTRICT M'.frame.rel M'.frame.world)^* x w ==> rooted_model M x M' /\ w IN M'.frame.world ==>
    ?n. heightLE M x M' w n``,
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[]
  >- (qexists_tac `0` >> rw[Once heightLE_cases])
  >- (`w IN M'.frame.world` by metis_tac[RESTRICT_def] >>
     `∃n. heightLE M x M' w n` by metis_tac[] >>
     qexists_tac `n + 1` >> rw[Once heightLE_cases] >>
     `w' IN M.frame.world`
         by (`(RESTRICT M'.frame.rel M'.frame.world)^* x w` by metis_tac[heightLE_RTC] >>
             `(RESTRICT M'.frame.rel M'.frame.world)^* x w'` by metis_tac[RTC_CASES2] >>
             metis_tac[rooted_model_def]) >>
     `∃w. w ∈ M.frame.world ∧ M.frame.rel w w' ∧ heightLE M x M' w n` suffices_by metis_tac[] >>
     qexists_tac `w` >> rw[]
     >- (`(RESTRICT M'.frame.rel M'.frame.world)^* x w` by
        metis_tac[heightLE_RTC] >>
        metis_tac[rooted_model_def])
     >- (`w IN M.frame.world` suffices_by metis_tac[rooted_model_def] >>
        `(RESTRICT M'.frame.rel M'.frame.world)^* x w` suffices_by metis_tac[rooted_model_def] >>
        metis_tac[heightLE_RTC])));

val rooted_have_height_applied = store_thm(
  "rooted_have_height_applied",
  ``!x w. rooted_model M x M' /\ w IN M.frame.world ==>
  {n| heightLE M x M' w n} <> {}``,
  rw[] >>
  `(RESTRICT M'.frame.rel M'.frame.world)^* x w /\ w IN M'.frame.world` by
  metis_tac[rooted_model_def] >>
  `?n. heightLE M x M' w n` by metis_tac[rooted_have_height] >>
  `n IN {n | heightLE M x M' w n}` by fs[] >>
  metis_tac[MEMBER_NOT_EMPTY]);

val heightLE_MIN_SET_IN = store_thm(
  "heightLE_MIN_SET_IN",
  ``!x w. rooted_model M x M' /\ w IN M.frame.world ==>
  MIN_SET {n| heightLE M x M' w n} IN {n| heightLE M x M' w n}``,
  rpt strip_tac >>
  `{n| heightLE M x M' w n} <> {}` by metis_tac[rooted_have_height_applied] >>
  metis_tac[MIN_SET_LEM]);



val height_heightLE = store_thm(
  "height_heightLE",
  ``!M x M' w n. rooted_model M x M' ==>
  w IN M.frame.world ==> height M x M' w = n ==> heightLE M x M' w n``,
  rpt strip_tac >>
  fs[height_def] >>
  `w ∈ M'.frame.world ∧
  (RESTRICT M'.frame.rel M'.frame.world)^* x w` by metis_tac[rooted_model_def] >>
  `?n. heightLE M x M' w n` by metis_tac[rooted_have_height] >>
  `n' IN {n | heightLE M x M' w n}` by fs[] >>
  `{n | heightLE M x M' w n} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `(MIN_SET {n | heightLE M x M' w n}) IN {n | heightLE M x M' w n}` by metis_tac[MIN_SET_LEM] >>
  fs[] >> rw[]);

val lemma_2_33 = store_thm(
  "lemma_2_33",
  ``!M x M' k. rooted_model M x M' ==>
  !w. w IN (hrestriction M x M' k).frame.world ==> ?f. nbisim (hrestriction M x M' k) M f (k - height M x M' w) w w``,
rw[] >> qexists_tac `λn w1 w2. w1 = w2 /\ height M x M' w1 <= k - n` >> rw[nbisim_def] (* 9 *)
>- fs[hrestriction_def]
>- (`height M x M' w <= k` by fs[hrestriction_def] >>
   `k - (k − height M x M' w) = height M x M' w` by fs[] >>
   fs[])
>- fs[satis_def,hrestriction_def,IN_DEF]
>- fs[hrestriction_def]
>- fs[hrestriction_def]
>- (fs[hrestriction_def,height_def] >>
   `(RESTRICT M'.frame.rel M'.frame.world)^* x w1'` by metis_tac[rooted_model_def] >>
   `w1' IN M'.frame.world` by metis_tac[rooted_model_def] >>
   `{n | heightLE M x M' w1' n} <> {}`
       by (`?n. heightLE M x M' w1' n` by metis_tac[rooted_have_height] >>
          `n' IN {n | heightLE M x M' w1' n}` by fs[] >>
          metis_tac[MEMBER_NOT_EMPTY]) >>
   `{n | heightLE M x M' w2 n} <> {}`
       by (`w2 IN M'.frame.world` by metis_tac[rooted_model_def] >>
          `(RESTRICT M'.frame.rel M'.frame.world)^* x w2` by metis_tac[rooted_model_def] >>
          `?n. heightLE M x M' w2 n` by metis_tac[rooted_have_height] >>
          `n' IN {n | heightLE M x M' w2 n}` by fs[] >>
          metis_tac[MEMBER_NOT_EMPTY]) >>
   `(MIN_SET {n | heightLE M x M' w2 n}) IN {n | heightLE M x M' w2 n}` by metis_tac[MIN_SET_LEM] >>
   fs[] >>
   `heightLE M x M' w1' ((MIN_SET {n | heightLE M x M' w2 n}) + 1)`
       by (rw[Once heightLE_cases] >> metis_tac[]) >>
   `(MIN_SET {n | heightLE M x M' w2 n} + 1) IN
   {n | heightLE M x M' w1' n}` by fs[] >>
   `(MIN_SET {n | heightLE M x M' w1' n}) <=
   (MIN_SET {n | heightLE M x M' w2 n} + 1)` by metis_tac[MIN_SET_LEM] >>
   qabbrev_tac `a = MIN_SET {n | heightLE M x M' w2 n}` >>
   qabbrev_tac `b = MIN_SET {n | heightLE M x M' w1' n}` >>
   `b <= k − (n + 1) + 1` by fs[] >>
   `k > n` suffices_by rw[] >>
   `k - n >= 1` suffices_by fs[] >>
   fs[])
>- (fs[hrestriction_def] >>
   `k > n`
       by (`k - n >= 1` suffices_by fs[] >> fs[]) >>
   `k - (n + 1) + 1 = k - n` by fs[] >>
   `height M x M' w2' <= k - n` suffices_by fs[] >>
   fs[height_def] >>
   qabbrev_tac `a = MIN_SET {n | heightLE M x M' w2 n}` >>
   qabbrev_tac `b = MIN_SET {n | heightLE M x M' w2' n}` >>
   `a IN {n | heightLE M x M' w2 n}` by metis_tac[Abbr`a`,heightLE_MIN_SET_IN] >>
   fs[] >>
   `heightLE M x M' w2' (a + 1)` by metis_tac[heightLE_rel] >>
   `(a + 1) IN {n | heightLE M x M' w2' n}` by fs[] >>
   `{n | heightLE M x M' w2' n} <> {}` by metis_tac[rooted_have_height_applied] >>
   `b <= a + 1` by metis_tac[Abbr`b`,MIN_SET_LEM] >>
   fs[])
>- fs[hrestriction_def]
>- (fs[hrestriction_def,height_def] >>
   qabbrev_tac `a = MIN_SET {n | heightLE M x M' w2 n}` >>
   qabbrev_tac `b = MIN_SET {n | heightLE M x M' w2' n}` >>
   `b <= a + 1`
       by (`{n | heightLE M x M' w2 n} <> {}` by metis_tac[rooted_have_height_applied] >>
          `a IN {n | heightLE M x M' w2 n}` by metis_tac[Abbr`b`,MIN_SET_LEM] >>
          fs[] >>
          `heightLE M x M' w2' (a + 1)` by metis_tac[heightLE_rel] >>
          `{n | heightLE M x M' w2' n} <> {}` by metis_tac[rooted_have_height_applied] >>
          `(a + 1) IN {n | heightLE M x M' w2' n}` by fs[] >>
          metis_tac[Abbr`b`,MIN_SET_LEM]) >>
   `k > n`
       by (`k - n >= 1` suffices_by fs[] >> fs[]) >> fs[]));






val point_GENSUBMODEL_def = Define`
  point_GENSUBMODEL M w =
   <| frame := <| world := {v | v IN M.frame.world /\ (RESTRICT M.frame.rel M.frame.world)^* w v };
rel := λw1 w2. w1 IN M.frame.world /\ w2 IN M.frame.world /\ M.frame.rel w1 w2|>;
          valt := M.valt |>`;

val point_GENSUBMODEL_GENSUBMODEL = store_thm(
  "point_GENSUBMODEL_GENSUBMODEL",
  ``!M w. w IN M.frame.world ==> GENSUBMODEL (point_GENSUBMODEL M w) M``,
  rw[GENSUBMODEL_def,point_GENSUBMODEL_def] (* 2 *)
  >- (rw[SUBMODEL_def] >> fs[SUBSET_DEF])
  >- (simp[Once RTC_CASES2] >>
     `∃u. (RESTRICT M.frame.rel M.frame.world)^* w u ∧ RESTRICT M.frame.rel M.frame.world u w2` suffices_by metis_tac[] >>
     qexists_tac `w1` >> simp[Once RESTRICT_def]));


val point_GENSUBMODEL_rooted = store_thm(
  "point_GENSUBMODEL_rooted",
  ``!M w. w IN M.frame.world ==> rooted_model (point_GENSUBMODEL M w) w M``,
  rw[rooted_model_def] >> eq_tac >> rw[] (* 7 *)
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]
  >- (fs[point_GENSUBMODEL_def] >> metis_tac[RESTRICT_def])
  >- (fs[point_GENSUBMODEL_def] >> metis_tac[RESTRICT_def])
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]);

val point_GENSUBMODEL_satis = store_thm(
  "point_GENSUBMODEL_satis",
  ``!M w f. satis M w f ==> satis (point_GENSUBMODEL M w) w f``,
  rw[] >>
  `w IN M.frame.world` by metis_tac[satis_in_world] >>
  `GENSUBMODEL (point_GENSUBMODEL M w) M` by metis_tac[point_GENSUBMODEL_GENSUBMODEL] >>
  `(RESTRICT M.frame.rel M.frame.world)^* w w` by metis_tac[RTC_CASES2] >>
  `w IN (point_GENSUBMODEL M w).frame.world` by fs[point_GENSUBMODEL_def] >>
  metis_tac[prop_2_6]);


val root_height_0 = store_thm(
  "root_height_0",
  ``!M x M'. rooted_model M x M' ==> height M x M' x = 0``,
  rw[Once heightLE_cases,height_def] >>
  `0 IN 𝕌(:num)` by fs[] >>
  `𝕌(:num) <> {}` by fs[] >>
  `MIN_SET 𝕌(:num) <= 0` by metis_tac[MIN_SET_LEM] >> fs[]);

val finite_image_lemma = Q.prove(
  `FINITE {x | P x} ==> FINITE { f x | P x }`,
  strip_tac >> `{ f x | P x } = IMAGE f { x | P x}` by simp[EXTENSION] >>
  metis_tac[IMAGE_FINITE]);

val DIAM_EQ_lemma = Q.prove(
  `∀a b. ◇ a = ◇ b ⇒ a = b`,
  Induct_on `a` >> rw[]);


val tree_like_model_rooted = store_thm(
  "tree_like_model_rooted",
  ``!M r. tree M.frame r ==> rooted_model M r M``,
  rw[rooted_model_def,tree_def] (* 2 *)
  >- rw[EQ_IMP_THM]
  >- rw[EQ_IMP_THM,RESTRICT_def]);






val tree_height_rel_lemma = store_thm(
  "tree_height_rel_lemma",
  ``!M x. tree M.frame x ==> !w. w IN M.frame.world /\ height M x M w = n ==>
                                !v. M.frame.rel w v /\ v IN M.frame.world ==> height M x M v = n + 1``,
  rw[] >> `rooted_model M x M` by metis_tac[tree_like_model_rooted] >> fs[tree_def] >>
  `(RESTRICT M.frame.rel M.frame.world)^* x w` by metis_tac[] >>
  `!x' w. (RESTRICT M.frame.rel M.frame.world)^* x' w ==> x = x' ==>
          !v. v IN M.frame.world ==> M.frame.rel w v ==> height M x M v = height M x M w + 1` suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] (* 2 *)
  >- (`height M x M x = 0` by metis_tac[root_height_0] >> fs[] >>
     rw[height_def] >>
     `(MIN_SET {n | heightLE M x M v' n}) IN {n | heightLE M x M v' n}` by metis_tac[heightLE_MIN_SET_IN] >> fs[] >>
     SPOSE_NOT_THEN ASSUME_TAC >>
     `MIN_SET {n | heightLE M x M v' n} > 1 \/ MIN_SET {n | heightLE M x M v' n} < 1` by fs[] (* 2 *)
     >- (`heightLE M x M v' 1`
            by (`heightLE M x M x 0` by fs[Once heightLE_cases] >>
               rw[Once heightLE_cases] >>
               `∃n. 1 = n + 1 ∧ ∃w. w ∈ M.frame.world ∧ M.frame.rel w v' ∧ heightLE M x M w n` suffices_by metis_tac[] >>
               simp[PULL_EXISTS] >> map_every qexists_tac [`0`,`x`] >> rw[]) >>
        `1 IN {n | heightLE M x M v' n}` by fs[] >>
        `{n | heightLE M x M v' n} <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
        `(MIN_SET {n | heightLE M x M v' n}) IN {n | heightLE M x M v' n}` by metis_tac[heightLE_MIN_SET_IN] >>
        `(MIN_SET {n | heightLE M x M v' n}) <= 1` by metis_tac[MIN_SET_LEM] >> fs[])
     >- (`MIN_SET {n | heightLE M x M v' n} = 0` by fs[] >>
        `(MIN_SET {n | heightLE M x M v' n}) IN {n | heightLE M x M v' n}` by metis_tac[heightLE_MIN_SET_IN] >>
        `heightLE M x M v' 0` by metis_tac[IN_DEF] >>
        fs[Once heightLE_cases] >> metis_tac[]))
  >- (rw[height_def] >> SPOSE_NOT_THEN ASSUME_TAC >>
     `MIN_SET {n | heightLE M x M v' n} > MIN_SET {n | heightLE M x M w'' n} + 1 \/
     MIN_SET {n | heightLE M x M v' n} < MIN_SET {n | heightLE M x M w'' n} + 1` by fs[] (* 2 *)
     >- (`heightLE M x M v' (MIN_SET {n | heightLE M x M w'' n} + 1)`
            by (rw[Once heightLE_cases] >>
               `v' <> x ==> ∃w. w ∈ M.frame.world ∧ M.frame.rel w v' ∧ heightLE M x M w (MIN_SET {n | heightLE M x M w'' n})` suffices_by metis_tac[] >> rw[] >> qexists_tac `w''` >> rw[] (* 2 *)
               >- metis_tac[RESTRICT_def]
               >- (`w'' IN M.frame.world` by metis_tac[RESTRICT_def] >>
                  `(MIN_SET {n | heightLE M x M w'' n}) IN {n | heightLE M x M w'' n}` by metis_tac[heightLE_MIN_SET_IN] >>
                  fs[])) >>
        `{n | heightLE M x M v' n} <> {}` by metis_tac[rooted_have_height_applied] >>
        `(MIN_SET {n | heightLE M x M w'' n} + 1) IN {n | heightLE M x M v' n}` by fs[IN_DEF] >>
        `MIN_SET {n | heightLE M x M v' n} <= MIN_SET {n | heightLE M x M w'' n} + 1` by metis_tac[MIN_SET_LEM] >> fs[])
     >- (`MIN_SET {n | heightLE M x M v' n} IN {n | heightLE M x M v' n}` by metis_tac[heightLE_MIN_SET_IN] >>
        `heightLE M x M v' (MIN_SET {n | heightLE M x M v' n})` by fs[IN_DEF] >>
        fs[Once heightLE_cases] (* 2 *)
        >- (`w'' IN M.frame.world` by metis_tac[RESTRICT_def] >>
           metis_tac[])
        >- (fs[EXISTS_UNIQUE_THM] >>
           `v' <> x` by (SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[]) >>
           `{n' | heightLE M x M v' n'} =
            {n' | v' = x ∨ ∃n''. n' = n'' + 1 ∧
                                 ∃w.  w ∈ M.frame.world ∧ M.frame.rel w v' /\ heightLE M x M w n''}` by fs[Once heightLE_cases] >>
           fs[] >>
           `n NOTIN {n | heightLE M x M w'' n}`
               by (SPOSE_NOT_THEN ASSUME_TAC >>
                  `w'' IN M.frame.world` by metis_tac[RESTRICT_def] >>
                  `{n | heightLE M x M w'' n} <> {}` by metis_tac[rooted_have_height_applied] >>
                  `MIN_SET {n | heightLE M x M w'' n} <= n` by metis_tac[MIN_SET_LEM] >> fs[]) >>
           `¬heightLE M x M w'' n` by fs[IN_DEF] >>
           `w''' = w''` suffices_by metis_tac[] >>
           `(∃t0. t0 ∈ M.frame.world ∧ M.frame.rel t0 v') ∧
             ∀t0 t0'.
            (t0 ∈ M.frame.world ∧ M.frame.rel t0 v') ∧
            t0' ∈ M.frame.world ∧ M.frame.rel t0' v' ⇒
            t0 = t0'` by metis_tac[] >>
            `w'' IN M.frame.world` by metis_tac[RESTRICT_def] >>
            `w'' = t0` by metis_tac[] >>
            `w''' = t0` by metis_tac[] >> fs[]))));



val tree_hrestriction_tree = store_thm(
  "tree_hrestriction_tree",
  ``!M x M. tree M.frame x ==> !n. tree (hrestriction M x M n).frame x``,
  rw[] (* 5 *) >> rw[tree_def,hrestriction_def] (* 5 *)
   >- fs[tree_def]
   >- (`rooted_model M x M` by metis_tac[tree_like_model_rooted] >>
      `height M x M x = 0` by metis_tac[root_height_0] >> fs[])
   >- (`rooted_model M x M` by metis_tac[tree_like_model_rooted] >>
      fs[tree_def] >>
      `(RESTRICT M.frame.rel M.frame.world)^* x t` by metis_tac[] >>
      `!x' t. (RESTRICT M.frame.rel M.frame.world)^* x' t ==> t IN M.frame.world ==> height M x' M t <= n ==> x' = x ==>
              (RESTRICT (λn1 n2. M.frame.rel n1 n2) {w | w ∈ M.frame.world ∧ height M x M w ≤ n})^* x' t` suffices_by metis_tac[] >>
      ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
      `t'' = x \/ ((RESTRICT (λn1 n2. M.frame.rel n1 n2) {w | w ∈ M.frame.world ∧ height M x M w ≤ n})^* x t' /\
      (RESTRICT (λn1 n2. M.frame.rel n1 n2) {w | w ∈ M.frame.world ∧ height M x M w ≤ n}) t' t'')` suffices_by metis_tac[RTC_CASES2] >>
      rw[] >>
      `t'' <> x ==>
      ((RESTRICT (λn1 n2. M.frame.rel n1 n2) {w | w ∈ M.frame.world ∧ height M x M w ≤ n})^* x t' /\
      (RESTRICT (λn1 n2. M.frame.rel n1 n2) {w | w ∈ M.frame.world ∧ height M x M w ≤ n}) t' t'')` suffices_by metis_tac[] >> rw[]
      >- (last_x_assum irule (* 2 *)
         >- (`t' IN M.frame.world /\ t'' IN M.frame.world /\ M.frame.rel t' t''` by metis_tac[RESTRICT_def] >>
            `tree M.frame x` by rw[tree_def] >>
            `height M x M t'' = height M x M t' + 1` by metis_tac[tree_height_rel_lemma] >>
            fs[])
         >- metis_tac[RESTRICT_def])
      >- (rw[RESTRICT_def] (* 3 *)
         >- metis_tac[RESTRICT_def]
         >- metis_tac[RESTRICT_def]
         >- (`t' IN M.frame.world /\ t'' IN M.frame.world /\ M.frame.rel t' t''` by metis_tac[RESTRICT_def] >>
            `tree M.frame x` by rw[tree_def] >>
            `height M x M t'' = height M x M t' + 1` by metis_tac[tree_height_rel_lemma] >>
            fs[])))
  >- metis_tac[tree_def]
  >- (`rooted_model M x M` by metis_tac[tree_like_model_rooted] >>
     fs[tree_def] >> `∃!t0. t0 ∈ M.frame.world ∧ M.frame.rel t0 t` by metis_tac[] >>
     `tree M.frame x` by rw[tree_def] >>
     fs[EXISTS_UNIQUE_THM] >> rw[] >>
     qexists_tac `t0` >> rw[] >>
     `height M x M t = height M x M t0 + 1` by metis_tac[tree_height_rel_lemma] >> fs[]));



Theorem BIGCONJ_subforms_DEG:
∀s.
         FINITE s ⇒
         ∀n s0.
             (∀f. f ∈ s ⇒ DEG f ≤ n) /\
             (!f. f IN s ==> (!a. (VAR a) IN (subforms f) ==> a IN s0))⇒
             ∃ff.
                 DEG ff ≤ n ∧
                 (!a. (VAR a) IN (subforms ff) ==> a IN s0) /\
                 (∀w M.
                      w ∈ M.frame.world ⇒
                      (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f))
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `TRUE` >> rw[TRUE_def,satis_def,DEG_def,subforms_def]) >>
`(∀f. f ∈ s ⇒ DEG f ≤ n) ∧
 (∀f. f ∈ s ⇒ ∀a. VAR a ∈ subforms f ⇒ a ∈ s0)` by metis_tac[] >>
first_x_assum drule_all >> strip_tac >>
qexists_tac `AND e ff` >> rw[AND_def,satis_AND,DEG_def,subforms_def] (* 3 *)>>
metis_tac[]
QED





Theorem prop_letters_subforms:
!phi p.
   (p IN (prop_letters phi)) <=> (VAR p) IN (subforms phi)
Proof
Induct_on `phi` >> rw[prop_letters_def,subforms_def]
QED

(*prettier version of 2.29 in terms of propositional letters*)

Theorem prop_2_29_prop_letters:
!s. FINITE s /\ INFINITE univ(:'b) ==> !n. FINITE (partition (equiv0 (μ:'b itself)) {f| DEG f <= n /\ prop_letters f ⊆ s})
Proof
rw[] >> drule prop_2_29_strengthen >> rw[] >>
`{f | DEG f ≤ n ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s} =
{f | DEG f ≤ n ∧ prop_letters f ⊆ s}` suffices_by metis_tac[] >>
rw[EXTENSION,SUBSET_DEF] >> metis_tac[prop_letters_subforms]
QED


Theorem rooted_model_same_frame:
!M M' x. M.frame = M'.frame ==>
         (rooted_model M x M <=> rooted_model M' x M')
Proof
rw[rooted_model_def]
QED


(*move to chap 1 later*)

Theorem prop_letters_FINITE:
!phi. FINITE (prop_letters phi)
Proof
Induct_on `phi` >> rw[prop_letters_def]
QED

Theorem thm_2_34:
!M1 w1:'b phi: chap1$form.
     satis M1 w1 phi ==>
         ?FM v:'b list. FINITE (FM.frame.world) /\
                        v IN FM.frame.world /\
                        satis FM v phi
Proof
rw[] >>
qabbrev_tac `k = DEG phi` >>
`∃M2 w2:'b list. tree M2.frame w2 ∧ satis M2 w2 phi` 
  by metis_tac[prop_2_15_corollary] >>
qabbrev_tac `M3 = hrestriction M2 w2 M2 k` >>
`rooted_model M2 w2 M2` by metis_tac[tree_like_model_rooted] >>
`w2 IN M3.frame.world`
  by 
   (fs[Abbr`M3`,hrestriction_def] >> rw[] >- metis_tac[satis_in_world]
    >- (`height M2 w2 M2 w2 = 0` by metis_tac[root_height_0] >> fs[])) >>
`∃f. nbisim M3 M2 f (k − height M2 w2 M2 w2) w2 w2`
  by
   (fs[Abbr`M3`] >> irule lemma_2_33 (* 2 *) >> fs[]) >>
`DEG phi <= k` by fs[Abbr`k`] >>
`height M2 w2 M2 w2 = 0` by metis_tac[root_height_0] >> fs[] >>
`satis M3 w2 phi` by metis_tac[prop_2_31_half1] >>
qabbrev_tac
  `M3' =
   <| frame := <| world := M3.frame.world ;
                    rel := M3.frame.rel ;
                |>;
       valt := \p v. if (p IN prop_letters phi) 
                        then (M3.valt p v) 
                     else F |>` >>
`satis M3' w2 phi`
  by
   (`satis M3 w2 phi <=> satis M3' w2 phi` suffices_by metis_tac[] >>
    irule exercise_1_3_1 >> rw[] (* 2 *)
    >- rw[Abbr`M3'`,FUN_EQ_THM]
    >- fs[Abbr`M3'`,frame_component_equality]) >>
    fs[Abbr`M3'`,frame_component_equality]) >>
  (* done with the first paragraph *)
qabbrev_tac `s = prop_letters phi` >>
`FINITE s`
  by metis_tac[Abbr`s`,prop_letters_FINITE] >>
  (*`FINITE univ(:'a)` by metis_tac[] >> *)
`INFINITE univ(:'b list)` by metis_tac[INFINITE_LIST_UNIV] >>
FREEZE_THEN drule
  (prop_2_29_strengthen |> INST_TYPE [beta |-> ``:'b list``]) >> strip_tac >>
qabbrev_tac `distfp = {f | DEG f ≤ k ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}//E μ` >>
`FINITE distfp` by metis_tac[] >>
`FINITE (IMAGE CHOICE distfp)` by metis_tac[FINITE_BIJ,CHOICE_BIJ_partition,equiv0_equiv_on] >>
qabbrev_tac
  `ss = PRIM_REC {w2}
                 (\s0:β list set n.
                      {CHOICE uset |
                      ?phi v. satis M3' v (DIAM phi) /\
                      ((DIAM phi) IN
                       (IMAGE CHOICE
                             ((IMAGE
                               (\s. s INTER {d | ?d0. d = DIAM d0})
                               distfp)
                               DELETE {})) /\
                      v IN s0 /\
                      uset = { u | M3'.frame.rel v u /\ u IN M3'.frame.world /\
                                   satis M3' u phi})})` >>
qabbrev_tac `W4 = BIGUNION {ss i| i <= k}` >>
qabbrev_tac `M4 = <| frame:= <| world := W4;
                                  rel := M3.frame.rel |>;
                        valt:= M3'.valt |>` >>
`M3.frame = M3'.frame` by rw[Abbr`M3'`,frame_component_equality] >>
  (* done with construction of M4 *)
`W4 SUBSET M3'.frame.world`
   by (rw[Abbr`W4`,Abbr`ss`,SUBSET_DEF] >> Cases_on `i` (* 2 *)
       >- fs[PRIM_REC_THM,Abbr`M3'`]
       >- (fs[PRIM_REC_THM] >>
           `?u. M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'` by metis_tac[satis_def] >>
           `u IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}` by fs[] >>
           `{u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'} <> {}`
             by metis_tac[MEMBER_NOT_EMPTY] >>
           `(CHOICE {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'})
              IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}`
             by metis_tac[CHOICE_DEF] >> fs[])) >>
(*proved W4 is subset of M3'*)
(* height ss issue *)
`!i a. a IN ss i ==> height M3' w2 M3' a = i`
  by
   (Induct_on `i` >> rw[] (* 2 *)
    >- (fs[Abbr`ss`,PRIM_REC_THM] >>
        `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
        `rooted_model M3 w2 M3` by metis_tac[Abbr`M3`,tree_like_model_rooted] >>
        (*need lemma same frame implies M3 rooted <=> M3' rooted, cheated! fixed*)
        `rooted_model M3' w2 M3'` by metis_tac[rooted_model_same_frame] >>
        metis_tac[root_height_0])
    >- (fs[Abbr`ss`,PRIM_REC_THM] >>
        `height M3' w2 M3' v = i` by metis_tac[] >>
        `{u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'} <> {}`
          by
           (fs[satis_def] >>
            rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `v'` >> rw[]) >>
        `(CHOICE
          {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}) IN
          {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}` by metis_tac[CHOICE_DEF] >>
        `!c.
           c IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}
                ==> height M3' w2 M3' c = SUC i`
          suffices_by metis_tac[] >> rw[] >>
        simp[ADD1] >>
        `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
        `tree M3.frame w2` by fs[Abbr`M3`] >>
        `tree M3'.frame w2` by metis_tac[] >>
        (*need little tree lemma, cheated! fixed*)
        `v IN M3'.frame.world` by metis_tac[satis_in_world] >>
        metis_tac[tree_height_rel_lemma])) >>
(*done with height issue*)
map_every qexists_tac [`M4`,`w2`] >>
rpt conj_tac (* 3 *)
(*FINITE M4.frame.world*)
>- (simp[Abbr`M4`,Abbr`W4`] >> rw[] (* 2 *)
    >- (`FINITE (count (k + 1))` by metis_tac[FINITE_COUNT] >>
        `{ss i | i ≤ k} = IMAGE ss (count (k + 1))`
          by
           (rw[EXTENSION] >>
            `!x. x <= k <=> x < k + 1` by fs[] >> metis_tac[]) >>
        metis_tac[IMAGE_FINITE]) >>
    Induct_on `i` >> simp[Abbr`ss`, PRIM_REC_THM] >> strip_tac >>
    qmatch_goalsub_abbrev_tac `PRIM_REC _ sf _` >> fs[] >>
    ho_match_mp_tac finite_image_lemma >>
    qabbrev_tac
          `ff = \(v,phi).
                {u | ∃phi'. phi = DIAM phi' /\ M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}` >>
    qmatch_abbrev_tac `FINITE bigset` >>
    `bigset SUBSET
           IMAGE ff
                 ((PRIM_REC {w2} sf i) CROSS
                  (IMAGE CHOICE ((IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp) DELETE {})))`
      by (rw[IMAGE_DEF,SUBSET_DEF] >> fs[Abbr`bigset`] >> simp[PULL_EXISTS] >>
          map_every qexists_tac [`(v,DIAM phi')`,`s'`] >>
          rw[] >> rw[Abbr`ff`] >> rw[EQ_IMP_THM,EXTENSION] (* 4 *)
          >- (qexists_tac `phi'` >> rw[])
          >- rw[]
          >- rw[]
          >- (`◇ phi' = ◇ phi''` by metis_tac[] >> metis_tac[DIAM_EQ_lemma])) >>
        (*subset proof end, the DIAM eq lemma applies since list universe is infinite*)
    `FINITE
      (PRIM_REC {w2} sf i ×
         (IMAGE CHOICE ((IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp) DELETE {})))`
      suffices_by metis_tac[SUBSET_FINITE,IMAGE_FINITE] >>
    irule FINITE_CROSS (* 2 *)
    >- rw[] >>
    `FINITE distfp` by metis_tac[] >>
    `FINITE (IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp)` by metis_tac[IMAGE_FINITE] >>
    `FINITE ((IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp) DELETE {})` by fs[] >>
    metis_tac[IMAGE_FINITE])
(*finiteness proof end*)
(*w2 IN M4.frame.world*)
>- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
(*in M4.frame.world proof end*)
(* the following is the critical part, prove satis M4 w2 phi *)
>- (`?f. nbisim M4 M3' f k w2 w2`
         suffices_by
          (rw[] >> `DEG phi <= k` by fs[Abbr`k`] >> metis_tac[prop_2_31_half1]) >>
    qexists_tac `\n a1 a2. a1 IN M4.frame.world /\ a2 IN M3'.frame.world /\
                 height M3' w2 M3' a1 = height M3' w2 M3' a2 /\
                 height M3' w2 M3' a1 <= k - n /\
                 (!phi. (DEG phi <= n /\ (∀a. VAR a ∈ subforms phi ⇒ a ∈ s))
                     ==> (satis M3' a1 phi <=> satis M3' a2 phi))` >>
    rw[nbisim_def] (* 8 *)
    >- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (`w2 IN M4.frame.world` suffices_by fs[Abbr`M4`,SUBSET_DEF] >>
        fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (`w2 IN M4.frame.world` suffices_by fs[Abbr`M4`,SUBSET_DEF] >>
        fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    (*the four trivial subgoal solved*)
    >- (* height M3 w2 M3 w2 = 0 *)
       (`tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
        `rooted_model M3 w2 M3` by metis_tac[Abbr`M3`,tree_like_model_rooted] >>
        `rooted_model M3' w2 M3'` by metis_tac[rooted_model_same_frame] >>
        (*need rooed lemma, cheated! fixed*)
        metis_tac[root_height_0])
    >- (`DEG (VAR p) = 0` by fs[DEG_def] >>
        first_x_assum drule >> strip_tac >> fs[subforms_def] >>
        Cases_on `p IN s` (* 2 *)
        >- (`satis M3' a1 (VAR p) <=> satis M3' a2 (VAR p)` by metis_tac[] >>
            `satis M4 a1 (VAR p) ⇔ satis M3' a1 (VAR p)` suffices_by metis_tac[] >>
            rw[satis_def,Abbr`M4`] >> fs[satis_def] >> metis_tac[SUBSET_DEF]) >>
        rw[satis_def,Abbr`M4`,Abbr`M3'`,Abbr`s`] >> fs[])
    (*remains two Hennessy-Milner style subgoal*)
    >- (SPOSE_NOT_THEN ASSUME_TAC >>
        `?phi. DEG phi ≤ n + 1 /\
               (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
               (satis M3' a1 phi /\ ¬satis M3' a2 phi)` suffices_by metis_tac[] >>
        `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
        `tree M3.frame w2` by rw[Abbr`M3`] >>
        `tree M3'.frame w2` by metis_tac[] (*lemma again, cheated! fixed*) >>
        `!a2'. a2' IN M3'.frame.world /\ M3'.frame.rel a2 a2' ==>
                 height M3' w2 M3' a1' = height M3' w2 M3' a2' /\ height M3' w2 M3' a2' ≤ k − n`
           by
            (rw[] (* 2 *)
             >- (`height M3' w2 M3' a2' = height M3' w2 M3' a2 + 1` by metis_tac[tree_height_rel_lemma] >>
                 `a1 IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                 `a1' IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                 `M3'.frame.rel a1 a1'` by fs[Abbr`M4`,Abbr`M3'`] >>
                 `height M3' w2 M3' a1' = height M3' w2 M3' a1 + 1` by metis_tac[tree_height_rel_lemma] >>
                 fs[])
             >- (`height M3' w2 M3' a2' = height M3' w2 M3' a2 + 1` by metis_tac[tree_height_rel_lemma] >>
                 fs[])) >>
        `∀a2'.
          a2' ∈ M3'.frame.world ⇒
          M3'.frame.rel a2 a2' ⇒
          ∃phi. DEG phi ≤ n ∧
                (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
                (satis M3' a1' phi /\ ¬satis M3' a2' phi)`
          by
           (rw[] >>
            `∃phi. DEG phi ≤ n ∧
             (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
             (satis M3' a1' phi ⇎ satis M3' a2' phi)` by metis_tac[] >>
            Cases_on `satis M3' a1' phi'` (* 2 *)
            >- (qexists_tac `phi'` >> metis_tac[satis_def])
            >- (qexists_tac `NOT phi'` >> rw[] (* 4 *)
                >- fs[DEG_def]
                >- fs[Abbr`s`,subforms_def]
                >- (`M4.frame.world SUBSET M3'.frame.world` by fs[Abbr`M4`] >>
                    `a1' IN M3'.frame.world` by fs[SUBSET_DEF] >>
                    metis_tac[satis_def])
                >- (`satis M3' a2' phi'` by metis_tac[] >> metis_tac[satis_def]))) >>
        (*big by tactic end*)
        qabbrev_tac
          `phis = {phi | ∃a2'. a2' ∈ M3'.frame.world ∧ M3'.frame.rel a2 a2' ∧ DEG phi ≤ n ∧
           (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
           satis M3' a1' phi ∧ ¬satis M3' a2' phi}` >>
        qabbrev_tac `rs = IMAGE CHOICE ((IMAGE (\s. s INTER phis) distfp) DELETE {})` >>
        `FINITE rs`
            by (`FINITE (IMAGE (λs. s ∩ phis) distfp)` by metis_tac[IMAGE_FINITE] >>
               `FINITE ((IMAGE (λs. s ∩ phis) distfp) DELETE {})` by metis_tac[FINITE_DELETE] >>
               metis_tac[IMAGE_FINITE,Abbr`rs`]) >>
        `!f. f IN rs ==> DEG f <= n`
            by
             (rw[Abbr`rs`] >> `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` by metis_tac[CHOICE_DEF] >>
              `(CHOICE (s' ∩ phis)) IN phis` by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
              fs[Abbr`phis`]) >>
        drule (BIGCONJ_subforms_DEG |> INST_TYPE [alpha |-> ``:'b list``]) >> rw[] >>
        `∀f. f ∈ rs ⇒ ∀a. VAR a ∈ subforms f ⇒ a ∈ s`
          by
           (rw[Abbr`rs`] >> fs[Abbr`distfp`,partition_def] >> rw[] >>
            `CHOICE
             ({y |
               (DEG y ≤ k ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y} ∩
              phis) IN
             ({y |
               (DEG y ≤ k ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y} ∩
              phis)` by metis_tac[CHOICE_DEF] >>
            fs[]) >>
        `∃ff.
           DEG ff ≤ n ∧
           (∀a. VAR a ∈ subforms ff ⇒ a ∈ s) /\
           (∀(w:'b list) M.
               w ∈ M.frame.world ⇒
               (satis M w ff ⇔ ∀f. f ∈ rs ⇒ satis M w f))` by metis_tac[] >>
        qexists_tac `DIAM ff` >> rw[] (* 4 *)
        >- fs[DEG_def]
        >- (fs[Abbr`s`,subforms_def])
        >- (rw[satis_def] (* 2 *)
            >- (fs[SUBSET_DEF,Abbr`M4`] >> metis_tac[Abbr`M4`])
            >- (qexists_tac `a1'` >> rw[] (* 3 *)
                >- fs[SUBSET_DEF,Abbr`M4`,Abbr`M3'`]
                >- fs[SUBSET_DEF,Abbr`M4`,Abbr`M3'`]
                >- (`a1' IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                    `∀f. f ∈ rs ⇒ satis M3' a1' f` suffices_by metis_tac[] >>
                    rw[Abbr`rs`,IMAGE_DEF] >>
                    `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` by metis_tac[CHOICE_DEF] >>
                    `(CHOICE (s' ∩ phis)) IN phis` by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
                    fs[Abbr`phis`])))
        >- (rw[satis_def] >>
            `!v. M3'.frame.rel a2 v /\ v IN M3'.frame.world
                 ==> ¬satis M3' v ff` suffices_by metis_tac[] >> rw[] >>
            `∃phi. DEG phi ≤ n ∧ (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
                   satis M3' a1' phi ∧ ¬satis M3' v phi` by metis_tac[] >>
            `equiv0 μ equiv_on {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}`
              by metis_tac[equiv0_equiv_on] >>
            `BIGUNION (partition (equiv0 μ) {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)})
             = {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by
              metis_tac[BIGUNION_partition] >>
            fs[BIGUNION] >> `n <= k` by fs[] >>
            `DEG phi' <= k` by fs[] >>
            `phi' IN {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by fs[] >>
            `phi' IN {x | ∃s'. s' ∈ {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}//E μ ∧ x ∈ s'}`
               by metis_tac[] >> fs[] >>
            qexists_tac `CHOICE (s' INTER phis)` >> rw[] (* 2 *)
            >- (rw[Abbr`rs`,IMAGE_DEF] >> simp[PULL_EXISTS] >> qexists_tac `s'` >> rw[] (* 2 *)
                >- fs[Abbr`distfp`]
                >- (`phi' IN phis` by (fs[Abbr`phis`] >> qexists_tac `v` >> rw[]) >>
                    `phi' IN (s' ∩ phis)` by metis_tac[IN_INTER] >> metis_tac[MEMBER_NOT_EMPTY]))
            >- (`s' ∩ phis <> {}`
                  by (`phi' IN phis` by (fs[Abbr`phis`] >> qexists_tac `v` >> rw[]) >>
                     `phi' IN (s' ∩ phis)` by metis_tac[IN_INTER] >> metis_tac[MEMBER_NOT_EMPTY]) >>
                `(CHOICE (s' ∩ phis)) IN (s' ∩ phis)` by metis_tac[CHOICE_DEF] >>
                `(CHOICE (s' ∩ phis)) IN s'` by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
                `equiv0 μ phi' (CHOICE (s' ∩ phis))` by metis_tac[partition_elements_interrelate] >>
                fs[equiv0_def])))
    >- (qabbrev_tac
          `phis = {phi | DEG phi <= n /\
                         (∀a. VAR a ∈ subforms phi ⇒ a ∈ s) /\
                         satis M3' a2' phi}` >>
        qabbrev_tac `rs = IMAGE CHOICE ((IMAGE (\s. s INTER phis) distfp) DELETE {})` >>
        `FINITE rs`
            by (`FINITE (IMAGE (λs. s ∩ phis) distfp)` by metis_tac[IMAGE_FINITE] >>
               `FINITE ((IMAGE (λs. s ∩ phis) distfp) DELETE {})` by metis_tac[FINITE_DELETE] >>
               metis_tac[IMAGE_FINITE,Abbr`rs`]) >>
        `!f. f IN rs ==> DEG f <= n`
            by (rw[Abbr`rs`] >> `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` by metis_tac[CHOICE_DEF] >>
               `(CHOICE (s' ∩ phis)) IN phis` by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
               fs[Abbr`phis`]) >>
        `∀f. f ∈ rs ⇒ ∀a. VAR a ∈ subforms f ⇒ a ∈ s`
          by
           (rw[Abbr`rs`] >> fs[Abbr`distfp`,partition_def] >> rw[] >>
            `CHOICE
             ({y |
               (DEG y ≤ k ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y} ∩
              phis) IN
             ({y |
               (DEG y ≤ k ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧ equiv0 μ x y} ∩
              phis)` by metis_tac[CHOICE_DEF] >>
            fs[]) >>
        (*cheated! same point as above fixed*)
        drule (BIGCONJ_subforms_DEG |> INST_TYPE [alpha |-> ``:'b list``]) >> rw[] >>
        `∃ff.
           DEG ff ≤ n ∧
           (∀a. VAR a ∈ subforms ff ⇒ a ∈ s) /\
           (∀(w:'b list) M.
               w ∈ M.frame.world ⇒
               (satis M w ff ⇔ ∀f. f ∈ rs ⇒ satis M w f))` by metis_tac[] >>
        `satis M3' a2' ff`
            by (fs[] >> rw[Abbr`rs`] >>
               `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` by metis_tac[CHOICE_DEF] >>
               `(CHOICE (s' ∩ phis)) IN phis` by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
               fs[Abbr`phis`]) >>
        `satis M3' a2 (DIAM ff)`
            by (rw[satis_def] >> qexists_tac `a2'` >> rw[]) >>
        `DEG (DIAM ff) <= n + 1` by fs[DEG_def] >>
        `∀a. VAR a ∈ subforms (DIAM ff) ⇒ a ∈ s` by fs[subforms_def] >>
        `satis M3' a1 (DIAM ff)` by metis_tac[] >>
        simp[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >>
        map_every qexists_tac [`CHOICE {u | M3'.frame.rel a1 u /\ satis M3' u ff}`,
                               `height M3' w2 M3' a1 + 1`,`height M3' w2 M3' a1 + 1`] >>
        rw[] (* 6 *)
        >- (`(height M3' w2 M3' a2 + 1) = SUC (height M3' w2 M3' a2)` by fs[] >>
            rw[Abbr`ss`,PRIM_REC_THM] >>
            qexists_tac `{u | M3'.frame.rel a1 u ∧ satis M3' u ff}` >> rw[] >> simp[PULL_EXISTS] >>
            `∃v s phi'.
             satis M3' v (◇ phi') ∧ ◇ phi' = CHOICE (s ∩ {d | ∃d0. d = ◇ d0}) ∧
             s ∈ distfp ∧ s ∩ {d | ∃d0. d = ◇ d0} ≠ ∅ ∧
             v ∈
              PRIM_REC {w2}
             (λs0 n'.
             {CHOICE uset |
             ∃phi' v s.
             satis M3' v (◇ phi') ∧
             ◇ phi' = CHOICE (s ∩ {d | ∃d0. d = ◇ d0}) ∧ s ∈ distfp ∧
             s ∩ {d | ∃d0. d = ◇ d0} ≠ ∅ ∧ v ∈ s0 ∧
             uset =
             {u |
              M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}})
             (height M3' w2 M3' a2) ∧
             {u | M3'.frame.rel a1 u ∧ satis M3' u ff} =
             {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}` suffices_by metis_tac[] >>
            qexists_tac `a1` >>
            `equiv0 μ equiv_on {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}`
              by metis_tac[equiv0_equiv_on] >>
            `BIGUNION (partition (equiv0 μ) {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}) =
             {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by metis_tac[BIGUNION_partition] >>
            fs[BIGUNION] >>
            `DEG (DIAM ff) <= k` by fs[DEG_def] >>
            `∀a. VAR a ∈ subforms (DIAM ff) ⇒ a ∈ s` by fs[subforms_def] >>
            `(DIAM ff) IN {f | DEG f ≤ k ∧ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by fs[] >>
            `(DIAM ff) IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}//E μ ∧
                               x ∈ s'}` by metis_tac[] >> fs[] >>
            qexists_tac `s''` >> rw[] >>
            `s'' ∩ {d | ∃d0. d = ◇ d0} <> {}`
               by (`(DIAM ff) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by fs[IN_INTER,IN_DEF] >>
                    metis_tac[MEMBER_NOT_EMPTY]) >>
            `(CHOICE (s'' ∩ {d | ∃d0. d = ◇ d0})) IN (s'' ∩ {d | ∃d0. d = ◇ d0})`
               by metis_tac[CHOICE_DEF] >>
            fs[] >> rw[] (* 4 *)
            >- (fs[equiv0_def,partition_def] >>
                `(◇ ff) ∈ {y | (DEG y ≤ k ∧ ∀a. VAR a ∈ subforms y ⇒ a ∈ s) ∧
                               ∀M w:β list. satis M w x ⇔ satis M w y}` by metis_tac[] >>
                fs[] >>
                `satis M3' a1 x` by metis_tac[] >> rw[] >>
                fs[])
            >- rw[Abbr`distfp`]
            >- (`height M3' w2 M3' a1 = i` by metis_tac[] >>
                fs[PULL_EXISTS])
            >- (`(DIAM d0) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by metis_tac[CHOICE_DEF] >>
                `(DIAM d0) IN s''` by metis_tac[IN_INTER] >>
                fs[partition_def] >> rw[] >>
                (*`◇ ff ∈ {y | DEG y ≤ k ∧ equiv0 μ x y} /\ ◇ d0 IN {y | DEG y ≤ k ∧ equiv0 μ x y}` by metis_tac[] >> fs[] >>*)
                (*`(DIAM ff) IN {f | DEG f ≤ k} /\ (DIAM d0) IN {f | DEG f ≤ k}` by fs[] >>*)
                fs[] >>
                `equiv0 μ (DIAM ff) (DIAM d0)` by metis_tac[equiv0_def] >>
                `INFINITE univ(:'b list)` by metis_tac[INFINITE_LIST_UNIV] >>
                `equiv0 μ ff d0` by metis_tac[equiv0_DIAM] >>
                fs[equiv0_def] >> rw[Once EXTENSION,Once EQ_IMP_THM] >> metis_tac[satis_in_world]))
          (* one out of 6 solved*)
(* 2nd of 6 *)
>- (fs[satis_def] >>
    `{u | M3'.frame.rel a1 u ∧ satis M3' u ff} <> {}`
      by
       (rw[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `v'` >> rw[]) >>
    `(CHOICE {u | M3'.frame.rel a1 u ∧ satis M3' u ff}) IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
      by metis_tac[CHOICE_DEF] >>
    `!c. c IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff} ==> M3.frame.rel a1 c`
      suffices_by metis_tac[] >> fs[Abbr`M3'`])
(* 3rd out of 6 *)
>-  (`(height M3' w2 M3' a2 + 1) = SUC (height M3' w2 M3' a2)` by fs[] >>
     rw[Abbr`ss`,PRIM_REC_THM] >>
     qexists_tac `{u | M3'.frame.rel a1 u ∧ satis M3' u ff}` >> rw[] >> simp[PULL_EXISTS] >>
     `∃v s phi'.
           satis M3' v (◇ phi') ∧ ◇ phi' = CHOICE (s ∩ {d | ∃d0. d = ◇ d0}) ∧
           s ∈ distfp ∧ s ∩ {d | ∃d0. d = ◇ d0} ≠ ∅ ∧
            v ∈
              PRIM_REC {w2}
             (λs0 n'.
             {CHOICE uset |
             ∃phi' v s.
             satis M3' v (◇ phi') ∧
             ◇ phi' = CHOICE (s ∩ {d | ∃d0. d = ◇ d0}) ∧ s ∈ distfp ∧
             s ∩ {d | ∃d0. d = ◇ d0} ≠ ∅ ∧ v ∈ s0 ∧
             uset =
             {u |
              M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}})
             (height M3' w2 M3' a2) ∧
             {u | M3'.frame.rel a1 u ∧ satis M3' u ff} =
             {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}` suffices_by metis_tac[] >>
     qexists_tac `a1` >>
     `equiv0 μ equiv_on {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by metis_tac[equiv0_equiv_on] >>
     `BIGUNION (partition (equiv0 μ) {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}) =
      {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by metis_tac[BIGUNION_partition] >>
     fs[BIGUNION] >>
     `DEG (DIAM ff) <= k` by fs[DEG_def] >>
     `∀a. VAR a ∈ subforms (DIAM ff) ⇒ a ∈ s` by fs[subforms_def] >>
     `(DIAM ff) IN {f | DEG f ≤ k /\ (∀a. VAR a ∈ subforms f ⇒ a ∈ s)}` by fs[] >>
     `(DIAM ff) IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}//E μ ∧
                        x ∈ s'}` by metis_tac[] >> fs[] >>
     qexists_tac `s''` >> rw[] >>
     `s'' ∩ {d | ∃d0. d = ◇ d0} <> {}`
               by
                (`(DIAM ff) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by fs[IN_INTER,IN_DEF] >>
                 metis_tac[MEMBER_NOT_EMPTY]) >>
     `(CHOICE (s'' ∩ {d | ∃d0. d = ◇ d0})) IN (s'' ∩ {d | ∃d0. d = ◇ d0})`
               by metis_tac[CHOICE_DEF] >>
     fs[] >> rw[] (* 4 *)
     >- (fs[equiv0_def,partition_def] >> rw[] >>
              (*`(◇ ff) ∈ {y | DEG y ≤ k ∧ ∀M w:'b list. satis M w x ⇔ satis M w y}` by metis_tac[] >>*)
         fs[] (*>>
         `satis M3' a1 (DIAM d0)` by metis_tac[] >>
              `(DIAM d0) ∈ {y | DEG y ≤ k ∧ ∀M w:'b list. satis M w (DIAM ff) ⇔ satis M w y}` by metis_tac[] >> fs[]*))
     >- rw[Abbr`distfp`]
     >- (`height M3' w2 M3' a1 = i` by metis_tac[] >>
         fs[PULL_EXISTS])
     >- (`(DIAM d0) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by metis_tac[CHOICE_DEF] >>
         `(DIAM d0) IN s''` by metis_tac[IN_INTER] >>
         fs[partition_def] >> rw[] >>
         (*`◇ ff ∈ {y | DEG y ≤ k ∧ equiv0 μ x y} /\ ◇ d0 IN {y | DEG y ≤ k ∧ equiv0 μ x y}` by metis_tac[] >> *)
         fs[] >>
         (* `(DIAM ff) IN {f | DEG f ≤ k} /\ (DIAM d0) IN {f | DEG f ≤ k}` by fs[] >>*)
         `equiv0 μ (DIAM ff) (DIAM d0)` by metis_tac[equiv0_def] >>
         `INFINITE univ(:'b list)` by metis_tac[INFINITE_LIST_UNIV] >>
         `equiv0 μ ff d0` by metis_tac[equiv0_DIAM] >>
         fs[equiv0_def] >> rw[Once EXTENSION,Once EQ_IMP_THM] >> metis_tac[satis_in_world]))
(* 4th out of 6 *)
>- (fs[satis_def] >>
    `{u | M3'.frame.rel a1 u ∧ satis M3' u ff} <> {}`
      by
       (`?u. u IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `v'` >> rw[]) >>
    `(CHOICE {u | M3'.frame.rel a1 u ∧ satis M3' u ff}) IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
      by metis_tac[CHOICE_DEF] >>
    `!c. c IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff} ==> height M3' w2 M3' c = height M3' w2 M3' a2'`
      suffices_by metis_tac[] >> rw[] >>
    `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
    `tree M3.frame w2` by fs[Abbr`M3`] >>
    `tree M3'.frame w2` by metis_tac[] (* fixed *) >>
    `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
    `height M3' w2 M3' c = height M3' w2 M3' a1 + 1` by metis_tac[tree_height_rel_lemma] >>
    `height M3' w2 M3' a2' = height M3' w2 M3' a1 + 1` by metis_tac[tree_height_rel_lemma] >> fs[])
(* 5th out of 6 *)
>- (fs[satis_def] >>
    `{u | M3'.frame.rel a1 u ∧ satis M3' u ff} <> {}`
      by
       (`?u. u IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `v'` >> rw[]) >>
    `(CHOICE {u | M3'.frame.rel a1 u ∧ satis M3' u ff}) IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
      by metis_tac[CHOICE_DEF] >>
    `!c. c IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}
         ==> height M3' w2 M3' c ≤ k − n` suffices_by metis_tac[] >> rw[] >>
    `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
    `tree M3.frame w2` by fs[Abbr`M3`] >>
    `tree M3'.frame w2` by metis_tac[] >>
    `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
    `height M3' w2 M3' c = height M3' w2 M3' a1 + 1` by metis_tac[tree_height_rel_lemma] >> fs[])
(* 6th out of 6 *)
>- (fs[satis_def] >>
    `{u | M3'.frame.rel a1 u ∧ satis M3' u ff} <> {}`
      by
       (`?u. u IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `v'` >> rw[]) >>
    `(CHOICE {u | M3'.frame.rel a1 u ∧ satis M3' u ff}) IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
      by metis_tac[CHOICE_DEF] >>
    `!c. c IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}  ==> (satis M3' c phi' ⇔ satis M3' a2' phi')`
      suffices_by metis_tac[] >> rw[] >>
    SPOSE_NOT_THEN ASSUME_TAC >> Cases_on `satis M3' c phi'` (* 2 *)
    >- (`¬satis M3' a2' phi'` by metis_tac[] >>
        `satis M3' a2' (NOT phi')` by metis_tac[satis_def] >>
        `(NOT phi') IN phis` by (fs[Abbr`phis`] >> fs[DEG_def,subforms_def]) >>
        `?r. r IN rs /\ equiv0 μ r (NOT phi')`
         by
          (`DEG (NOT phi') <= n` by fs[DEG_def] >>
           `equiv0 μ equiv_on {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}`
             by metis_tac[equiv0_equiv_on] >>
           `BIGUNION (partition (equiv0 μ) {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}) =
            {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}`
             by metis_tac[BIGUNION_partition] >>
           fs[BIGUNION] >> `n <= k` by fs[] >>
           `DEG (NOT phi') <= k` by fs[] >>
           `(NOT phi') IN {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` by fs[subforms_def] >>
           `(NOT phi') IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}//E μ ∧
                               x ∈ s'}` by metis_tac[] >> fs[] >>
           rw[Abbr`rs`] >> simp[PULL_EXISTS] >> qexists_tac `s'` >> rw[] (* 3 *)
           >- rw[Abbr`distfp`]
           >- (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
               qexists_tac `(NOT phi')` >> metis_tac[IN_INTER])
           >- (`s' ∩ phis ≠ ∅`
                by
                 (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                  qexists_tac `(NOT phi')` >> metis_tac[IN_INTER]) >>
               `CHOICE (s' ∩ phis) IN (s' ∩ phis)` by metis_tac[CHOICE_DEF] >>
               `!f. f IN (s' ∩ phis) ==> equiv0 μ f (¬phi')` suffices_by metis_tac[] >> rw[] >>
               fs[partition_def] >> rw[] >>
               (*`¬phi' ∈ {y | DEG y ≤ k ∧ equiv0 μ x y} /\
                f' IN {y | DEG y ≤ k ∧ equiv0 μ x y}` by metis_tac[] >>*)
               fs[] >>
         (*`f' IN {f | DEG f ≤ k} /\ (NOT phi') IN {f | DEG f ≤ k}` by fs[] >>*)
               fs[equiv0_def])) (* by tactic ends *) >>
        `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
        `satis M3' c r` by metis_tac[] >>
        `satis M3' c (NOT phi')` by metis_tac[equiv0_def] >> metis_tac[satis_def])
    >- (`satis M3' a2' phi'` by metis_tac[] >>
        `phi' IN phis` by fs[Abbr`phis`] >>
        `?r. r IN rs /\ equiv0 μ r phi'` by
          (`equiv0 μ equiv_on {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}`
             by metis_tac[equiv0_equiv_on] >>
           `BIGUNION (partition (equiv0 μ) {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}) =
            {f | DEG f ≤ k /\ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` by metis_tac[BIGUNION_partition] >>
        fs[BIGUNION] >> `n <= k` by fs[] >>
        `DEG phi' <= k` by fs[] >>
        `phi' IN {f | DEG f ≤ k ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}` by fs[] >>
        `phi' IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ ∀a. VAR a ∈ subforms f ⇒ a ∈ s}//E μ ∧
                               x ∈ s'}` by metis_tac[] >> fs[] >>
        rw[Abbr`rs`] >> simp[PULL_EXISTS] >> qexists_tac `s'` >> rw[] (* 3 *)
        >- rw[Abbr`distfp`]
        >- (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `phi'` >>
            metis_tac[IN_INTER])
        >- (`s' ∩ phis ≠ ∅` by
             (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `phi'` >>
              metis_tac[IN_INTER]) >>
            `CHOICE (s' ∩ phis) IN (s' ∩ phis)` by metis_tac[CHOICE_DEF] >>
            `!f. f IN (s' ∩ phis) ==> equiv0 μ f (phi')` suffices_by metis_tac[] >> rw[] >>
            fs[partition_def] >> rw[] >> fs[] >>
            (*`phi' ∈ {y | DEG y ≤ k ∧ equiv0 μ x y} /\ f' IN {y | DEG y ≤ k ∧ equiv0 μ x y}` by metis_tac[] >>
         fs[] >>
         `f' IN {f | DEG f ≤ k} /\ (phi') IN {f | DEG f ≤ k}` by fs[] >>*)
            fs[equiv0_def])) (* by tactic ends *) >>
        `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
        `satis M3' c r` by metis_tac[] >>
        `satis M3' c phi'` by metis_tac[equiv0_def])))));


Theorem peval_satis_strengthen':
!f M w. propform f /\ (prop_letters f ⊆ s) /\
        w IN M.frame.world ==>
        (satis M w f <=> peval ((\a. w IN M.valt a ) ∩ s) f)
Proof
rw[] >> drule peval_satis_strengthen >> strip_tac >> first_x_assum irule (* 2 *)
>- (rw[] >> metis_tac[prop_letters_subforms,SUBSET_DEF]) >>
rw[]
QED



Theorem example_2_23:
?M N w:num#num v:num#num. modal_eq M N w v /\ ¬(bisim_world M N w v)
Proof
qabbrev_tac
`M =
   <| frame := <| world := {(0,0)} ∪ {(n1,n2) | n2 <= n1 /\ n1 <> 0 /\ n2 <> 0};
                   rel := \p1 p2. (p1 = (0,0) /\ SND p2 = 1) \/
                                  (FST p1 = FST p2 /\ SND p2 = SND p1 + 1)
                |>;
       valt := \p v. F |>` >>
qabbrev_tac
`N =
   <| frame := <| world := {(0,n)| T} ∪ {(n1,n2) | n2 <= n1 /\ n1 <> 0 /\ n2 <> 0};
                   rel := \p1 p2. (p1 = (0,0) /\ SND p2 = 1) \/
                                  (FST p1 = FST p2 /\ SND p2 = SND p1 + 1)
                |>;
       valt := \p v. F |>` >>
map_every qexists_tac [`M`,`N`,`(0,0)`,`(0,0)`] >> rw[] (* 2 *)
>- (simp[modal_eq_tau] >>
   `!n. ?f. nbisim M N f n (0,0) (0,0)`
     by
      (rw[] >>
       qexists_tac
        `\m p1 p2.
            (SND p1 <= n-m /\ SND p2 <= n-m /\
             ((p1 = p2) \/
              (?k. p1 = (n,k) /\ p2 = (0,k))))` >> rw[nbisim_def](*8*)
       >- simp[satis_def,Abbr`M`,Abbr`N`]
       >- simp[satis_def,Abbr`M`,Abbr`N`]
       >- simp[satis_def,Abbr`M`,Abbr`N`]
       >- simp[satis_def,Abbr`M`,Abbr`N`]
       >- (qexists_tac `p1'` >> rw[] (* 4 *)
          >- fs[Abbr`M`,Abbr`N`]
          >- (fs[Abbr`N`,Abbr`M`] (* 16 all same *)
              >> Cases_on `p1'` >> Cases_on `p1` >> fs[SND,FST])
          >- (fs[Abbr`M`] (* 2 same *) >>
             Cases_on `p1'` >> Cases_on `p1` >> fs[SND,FST])
          >- (fs[Abbr`M`] (* 2 same *) >>
             Cases_on `p1'` >> Cases_on `p1` >> fs[SND,FST]))
       >- (`p1' = (n,k + 1)` by (Cases_on `p1'` >> fs[Abbr`M`,FST,SND]) >>(*cheated! trivial fixed*)
          qexists_tac `(0,k+1)` >> rw[] (* 2 same *) >>
          fs[Abbr`N`])
       >- (Cases_on `p1` >> Cases_on `q = 0` >> rw[] (*2*)
          >- (`r = 0` by fs[Abbr`M`] >> rw[] >> Cases_on `p2'` >>
              Cases_on `q = 0` >> rw[] (* 4 *)
              >- (`r = 1` by fs[Abbr`N`] >> rw[] >>
                  qexists_tac `(n,1)` >> rw[Abbr`M`])
              >- fs[Abbr`M`,Abbr`N`]
              >- (`r = 1` by fs[Abbr`N`] >> fs[Abbr`M`])
              >- (`r = 1` by fs[Abbr`N`] >> fs[])
              )
          >- (Cases_on `p2'` >>
             `q = q' ∧ r' = r + 1` by fs[Abbr`N`,FST,SND] >> rw[Abbr`M`] >>
             fs[Abbr`N`]))
       >- (Cases_on `p2'` >> rw[FST,SND] >> Cases_on `q = 0` >> rw[] (* 4 *)
          >- (`r = k + 1` by fs[Abbr`N`] >> rw[] >>
              qexists_tac `(n,k+1)` >> rw[Abbr`M`])
          >- fs[Abbr`M`,Abbr`N`]
          >- (`k = 0` by fs[Abbr`N`] >> rw[] >>
             `n = 0` by fs[Abbr`M`] >> fs[])
          >- (`r <= 1 /\ 1 <= n - m` suffices_by fs[] >>
             fs[Abbr`N`]))) >>
(*thankfully have found the n-bisimulation*)
rw[] >> `∃f. nbisim M N f (DEG form) (0,0) (0,0)` by metis_tac[] >>
irule prop_2_31_half1 >> qexists_tac `DEG form` >> fs[])
(*thankfully have proved modal equivalence...*)
>- (SPOSE_NOT_THEN ASSUME_TAC >> fs[bisim_world_def,bisim_def] >>
   `(0,1) IN N.frame.world` by fs[Abbr`N`] >>
   `N.frame.rel (0,0) (0,1)` by fs[Abbr`N`] >>
   `?v0. v0 IN M.frame.world /\ Z v0 (0,1) /\ M.frame.rel (0,0) v0`
     by metis_tac[] >>
   Cases_on `v0` >>
   `q <> 0` by fs[Abbr`M`] >> `r = 1` by fs[Abbr`M`] >> fs[] >>
   `!n. n <= q-1 ==> 1 <= n ==> Z (q,n) (0,n) ==> Z (q,n+1) (0,n+1)`
     by
      (rw[] >>
       `N.frame.rel (0,n) (0,n +1)` by fs[Abbr`N`] >>
       `(0,n) IN N.frame.world /\ (0,n + 1) IN N.frame.world` by fs[Abbr`N`] >>
       `(q,n) IN M.frame.world` by fs[Abbr`M`] >>
       `∀v'.
                v' ∈ N.frame.world ∧ N.frame.rel (0,n) v' ⇒
                ∃v. v ∈ M.frame.world ∧ Z v v' ∧ M.frame.rel (q,n) v`
       by metis_tac[] >>
       first_x_assum drule >> rw[] >>
       Cases_on `v` >> rw[] >>
       `(λp1 p2.
                        p1 = (0,0) ∧ SND p2 = 1 ∨
                        FST p1 = FST p2 ∧ SND p2 = SND p1 + 1) (q,n) (q',r)`
       by fs[Abbr`M`] >>
       `q = q' /\ r = n + 1` by fs[] >> rw[]) >>
   `!n. n <= q ==> 1 <= n ==> Z (q,n) (0,n)`
     by
      (Induct_on `n` >> rw[] >> Cases_on `n = 0` >> rw[] >>
       simp[arithmeticTheory.ADD1]) >>
   `Z (q,q) (0,q)` by fs[] >>
   `(0,q) IN N.frame.world /\ (0,q+1) IN N.frame.world /\
     N.frame.rel (0,q) (0,q+1)` by fs[Abbr`N`] >>
   `(q,q) IN M.frame.world` by fs[Abbr`M`] >>
   `∃v. v ∈ M.frame.world ∧ Z v (0,q+1) ∧ M.frame.rel (q,q) v` by metis_tac[] >>
   Cases_on `v` >> fs[Abbr`M`,FST,SND])
(*thankfully the goal is proved...*)
QED


val _ = export_theory();
