open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;


val _ = new_theory "prop2_29";


val (IBC_rules, IBC_ind, IBC_cases) = Hol_reln`
(!f1 f2 s.
IBC f1 s /\ IBC f2 s ==> IBC (DISJ f1 f2) s) /\
(!s. IBC FALSE s) /\
(!f s. IBC f s ==> IBC (NOT f) s) /\
(!f s. f IN s ==> IBC f s)`;

Theorem subst_prop_letters:
!phi σ1 σ2. 
   (!p. p IN prop_letters phi ==> σ1 p = σ2 p) ==>
   subst σ1 phi = subst σ2 phi
Proof
Induct_on `phi` (* 5 *) >> rw[subst_def,prop_letters_def]
QED



Theorem IBC_propform_EXISTS:
!fs. FINITE fs ==> 
  ?σ. 
   !phi. IBC phi fs ==>
        ?phi0. propform phi0 /\ 
               prop_letters phi0 ⊆ count (CARD fs) /\ 
               subst σ phi0 = phi
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `\p.ARB` >> rw[] >>
   `!phi. IBC phi ∅ ==>
       ∃phi0. propform phi0 /\ 
              prop_letters phi0 = ∅ ∧
              subst (λp. ARB) phi0 = phi`
     suffices_by metis_tac[] >>
   Induct_on `IBC` >> rw[] (* 4 *)
   >- (qexists_tac `DISJ phi0 phi0'` >> rw[] >> simp[prop_letters_def])
   >- (qexists_tac `FALSE` >> rw[subst_def,prop_letters_def])
   >- (qexists_tac `NOT phi0` >> rw[subst_def,prop_letters_def])
   >- metis_tac[NOT_IN_EMPTY])
>- (qabbrev_tac `n = (CARD fs)` >>
   rw[ADD1] >> 
   qexists_tac `\m. if m < n then σ m else e` >> 
   Induct_on `IBC` >> rw[] (* 4 *)
   >- (qexists_tac `DISJ phi0 phi0'` >> rw[] >> simp[prop_letters_def])
   >- (qexists_tac `FALSE` >> rw[subst_def,prop_letters_def])
   >- (qexists_tac `NOT phi0` >> rw[subst_def,prop_letters_def])
   >- (Cases_on `phi IN fs` (* 2 *)
      >- (`IBC phi fs` by metis_tac[IBC_rules] >> 
         first_x_assum drule >> rw[] >> qexists_tac `phi0` >>
         fs[count_def,SUBSET_DEF] >> rw[] (* 2 *)
         >- (`x < n` by metis_tac[] >> fs[])
         >- (irule subst_prop_letters >> rw[]))
      >- (`phi = e` by fs[INSERT_DEF] >>
         qexists_tac `VAR n` >> rw[prop_letters_def,subst_def])))
QED

Theorem subst_VAR:
!phi0 σ n. subst σ phi0 = VAR n ==>
           ?m. phi0 = VAR m /\ σ m = VAR n
Proof
Induct_on `phi0` >> rw[subst_def]
QED

Theorem subst_DISJ:
!phi0 σ phi1 phi2. subst σ phi0 = DISJ phi1 phi2 /\ (!p. VAR p <> phi0) ==>
           ?phi01 phi02. 
              phi0 = DISJ phi01 phi02 /\
              subst σ phi01 = phi1 /\ subst σ phi02 = phi2
Proof
Induct_on `phi0` >> rw[subst_def]
QED

Theorem subst_FALSE:
!phi0 σ. subst σ phi0 = ⊥ /\ (!p. VAR p <> phi0) ==>
         phi0 = FALSE
Proof
Induct_on `phi0` >> rw[subst_def]
QED

Theorem subst_NOT:
!phi0 σ phi. subst σ phi0 = ¬phi /\ (!p. VAR p <> phi0) ==>
         ?phi00. phi0 = NOT phi00 /\
                 subst σ phi00 = phi
Proof
Induct_on `phi0` >> rw[subst_def]
QED

Theorem subst_DIAM:
!phi0 σ phi. subst σ phi0 = ◇ phi /\ (!phi00. DIAM phi00 <> phi0) ==>
         ?p. phi0 = VAR p 
Proof
Induct_on `phi0` >> rw[subst_def]
QED

Theorem subst_propform_satis:
!phi σ phi0. subst σ phi0 = phi /\ propform phi0 ==>
    (!M w. w IN M.frame.world ==> (satis M w phi <=>
           peval (\p. satis M w (σ p)) phi0))
Proof
Induct_on `phi` (* 5 *)
>- (rw[subst_def,satis_def,peval_def] >>
   drule subst_VAR >> rw[] >> simp[peval_def,satis_def])
>- (rw[satis_def] >> 
   Cases_on `!p. VAR p <> phi0` (* 2 *)
   >- (drule subst_DISJ >> rw[] >> rw[peval_def] >> fs[propform_def] >> 
      `(satis M w (subst σ phi01) <=> peval (λp. satis M w (σ p)) phi01) /\
       (satis M w (subst σ phi02) <=> peval (λp. satis M w (σ p)) phi02)`
        suffices_by metis_tac[] >> 
      metis_tac[])
   >- (fs[] >> pop_assum (assume_tac o SYM) >> rw[] >> fs[subst_def,satis_def]))
>- (rw[] >>  Cases_on `!p. VAR p <> phi0` (* 2 *)
   >- (drule subst_FALSE >> rw[] >> rw[satis_def])
   >- (fs[] >> pop_assum (assume_tac o SYM) >> fs[subst_def]))
>- (rw[] >> Cases_on `!p. VAR p <> phi0` (* 2 *)
   >- (drule subst_NOT >> rw[] >> rw[peval_def,satis_def] >> fs[propform_def])
   >- (fs[] >> pop_assum (assume_tac o SYM) >> fs[subst_def]))
>- (rw[] >>
   `!phi00. DIAM phi00 <> phi0` by 
     (rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> pop_assum (assume_tac o SYM) >>
      fs[propform_def]) >>
   drule subst_DIAM >> rw[] >> fs[peval_def,subst_def])
QED



val peval_satis = store_thm(
"peval_satis",
``!M w f. propform f /\ w IN M.frame.world ==> (satis M w f <=> peval (λa. w IN M.valt a) f)``,
Induct_on `f` >> rw[]
>> metis_tac[satis_def]);

val equiv0_def = Define`
     equiv0 (:β) f1 f2 <=> !M w:β. satis M w f1 <=> satis M w f2`;


Theorem subst_equiv0:
!phi1 phi2. propform phi1 /\ propform phi2 /\ equiv0 (:β) phi1 phi2 ==>
    !σ. equiv0 (:β) (subst σ phi1) (subst σ phi2)
Proof
rw[equiv0_def] >> 
Cases_on `w IN M.frame.world` (* 2 *)
>- (`∀M w:β.
             w ∈ M.frame.world ⇒
             (satis M w (subst σ phi1) ⇔ peval (λp. satis M w (σ p)) phi1)`
     by metis_tac[subst_propform_satis] >>
   `∀M w:β.
             w ∈ M.frame.world ⇒
             (satis M w (subst σ phi2) ⇔ peval (λp. satis M w (σ p)) phi2)`
     by metis_tac[subst_propform_satis] >>
   rw[] >>
   qabbrev_tac `M' = 
                     <| frame := <| world := M.frame.world ;
                                      rel := M.frame.rel; |>;
                         valt := λp w. satis M w (σ p);|>` >>
   `∀M w:β.
            w ∈ M.frame.world ⇒
            (satis M w phi2 ⇔ peval (λa. w ∈ M.valt a) phi2)`
     by metis_tac[peval_satis] >>
   `∀M w:β.
            w ∈ M.frame.world ⇒
            (satis M w phi1 ⇔ peval (λa. w ∈ M.valt a) phi1)`
     by metis_tac[peval_satis] >>
   `w IN M'.frame.world` by fs[Abbr`M'`] >> 
   `(satis M' w phi2 ⇔ peval (λa. w ∈ M'.valt a) phi2) /\
    (satis M' w phi1 ⇔ peval (λa. w ∈ M'.valt a) phi1)` by metis_tac[] >>
   fs[Abbr`M'`] >> metis_tac[])
>- metis_tac[satis_in_world]
QED



val equiv0_equiv_on = store_thm(
  "equiv0_equiv_on",
  ``!s. (equiv0 (:β)) equiv_on s``,
  rw[equiv_on_def] >> metis_tac[equiv0_def]);

val equiv_on_same_partition = store_thm(
"equiv_on_same_partition",
``R equiv_on s ==> !x y. R x y ==> (!t1 t2. t1 IN partition R s /\ t2 IN partition R s /\ x IN t1 /\ y IN t2 ==> t1 = t2)``,
rw[partition_def,equiv_on_def] >> rw[EXTENSION,EQ_IMP_THM] >> fs[]
>> metis_tac[]);



Theorem IBC_INJ_propform_equiv0:
!fs σ. FINITE fs ==>
   (!phi. IBC phi fs ==> 
      ?phi0. 
           subst σ phi0 = phi /\ propform phi0 /\
           prop_letters phi0 ⊆ count (CARD fs)) ==> 
     INJ 
        (\phis.
            {f |f ⊆ count (CARD fs) /\
                peval f 
                    (CHOICE 
                          {phi0 | subst σ phi0 = CHOICE phis /\ 
                                  propform phi0 /\
                                  prop_letters phi0 ⊆ count (CARD fs)})})
        (partition (equiv0 (:β)) {phi | IBC phi fs})
        (POW (POW ((count (CARD fs)))))
Proof
rw[] >> rw[INJ_DEF] (* 2 *)
>- (qabbrev_tac `rphi = CHOICE phis` >>
   qabbrev_tac `rpf = (CHOICE
              {phi0 |
               subst σ phi0 = rphi ∧ propform phi0 ∧
               prop_letters phi0 ⊆ count (CARD fs)})` >>
   rw[SUBSET_DEF,POW_DEF])
>- (qabbrev_tac `rphi = CHOICE phis` >>
   qabbrev_tac `rpf = (CHOICE
              {phi0 |
               subst σ phi0 = rphi ∧ propform phi0 ∧
               prop_letters phi0 ⊆ count (CARD fs)})` >>
   qabbrev_tac `rphi' = CHOICE phis'` >>
   qabbrev_tac `rpf' = (CHOICE
              {phi0 |
               subst σ phi0 = rphi' ∧ propform phi0 ∧
               prop_letters phi0 ⊆ count (CARD fs)})` >>
   `rphi IN phis /\ rphi' IN phis'` by
     (`phis <> {} /\ phis' <> {}` suffices_by metis_tac[CHOICE_DEF] >>
      `{} NOTIN partition (equiv0 (:β)) {phi | IBC phi fs}`
        suffices_by metis_tac[] >>
      `(equiv0 (:β)) equiv_on {phi | IBC phi fs}` 
        suffices_by metis_tac[EMPTY_NOT_IN_partition] >>
      metis_tac[equiv0_equiv_on]) >> 
   `rpf IN {phi0 |
              subst σ phi0 = rphi ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)} /\
    rpf' IN {phi0 |
              subst σ phi0 = rphi' ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)}` by 
     (`{phi0 |
              subst σ phi0 = rphi ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)} <> {} /\ 
       {phi0 |
              subst σ phi0 = rphi' ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)} <> {}`
       suffices_by metis_tac[CHOICE_DEF] >>
      `(?phi0. phi0 IN 
           {phi0 |
              subst σ phi0 = rphi ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)}) /\ 
       (?phi0'. phi0' IN
           {phi0 |
              subst σ phi0 = rphi' ∧ propform phi0 ∧
              prop_letters phi0 ⊆ count (CARD fs)})`
        suffices_by metis_tac[NOT_IN_EMPTY] >>
       simp[] >>
      `IBC rphi fs /\ IBC rphi' fs` suffices_by metis_tac[] >>
      fs[partition_def] >> rfs[]) >>
   fs[] >> rfs[] >> 
   `equiv0 (:β) rphi rphi'` suffices_by 
     (strip_tac >>
      irule equiv_on_same_partition >> 
      map_every qexists_tac 
      [`equiv0 (:β)`,`{phi | IBC phi fs}`,`rphi`,`rphi'`] >> rw[] >>
      metis_tac[equiv0_equiv_on]) >>
   `equiv0 (:β) rpf rpf'` by 
     (rw[equiv0_def] >> Cases_on `w IN M.frame.world` (* 2 *)
      >- (qabbrev_tac 
           `M' = 
                <| frame := <| world := M.frame.world ;
                               rel := M.frame.rel ;
                               |>;
                    valt := \p v. if p IN (count (CARD fs)) 
                                     then (M.valt p v) 
                                  else F |>` >>
         `(satis M w rpf <=> satis M' w rpf) /\
          (satis M w rpf' <=> satis M' w rpf')`
           by 
            (rw[] >> irule exercise_1_3_1 >> rw[] (* 4 *)
             >- (rw[Abbr`M'`,FUN_EQ_THM] >> 
                `p < CARD fs` suffices_by metis_tac[] >> 
                fs[SUBSET_DEF,count_def])
             >- simp[frame_component_equality,Abbr`M'`]
             >- (rw[Abbr`M'`,FUN_EQ_THM] >> 
                `p < CARD fs` suffices_by metis_tac[] >> 
                fs[SUBSET_DEF,count_def])
             >- simp[frame_component_equality,Abbr`M'`]) >> 
         rw[] >> 
         `w IN M'.frame.world` by fs[Abbr`M'`] >>
         `(satis M' w rpf <=> peval (λa. w ∈ M'.valt a) rpf) /\ 
          (satis M' w rpf' <=> peval (λa. w ∈ M'.valt a) rpf')`
           by metis_tac[peval_satis] >> 
         rw[] >> 
         `(λa. w ∈ M'.valt a) IN 
          {f | f ⊆ count (CARD fs) ∧ peval f rpf} <=>
          (λa. w ∈ M'.valt a) IN 
          {f | f ⊆ count (CARD fs) ∧ peval f rpf'}`
           suffices_by 
             (fs[] >> rw[] >>
              `(λa. w ∈ M'.valt a) ⊆ count (CARD fs)` 
                suffices_by metis_tac[] >>
              rw[Abbr`M'`,count_def,SUBSET_DEF]) >>
         metis_tac[EXTENSION])
      >- metis_tac[satis_in_world]) >>
   `equiv0 (:β) (subst σ rpf) (subst σ rpf')` suffices_by metis_tac[] >>
   irule subst_equiv0 >> rw[])
QED  


Theorem IBC_FINITE_equiv0:
!fs. FINITE fs ==> FINITE (partition (equiv0 (:β)) {phi | IBC phi fs})
Proof
rw[] >> drule IBC_INJ_propform_equiv0 >> rw[] >> 
drule IBC_propform_EXISTS >> rw[] >> 
`INJ
              (λphis.
                   {f |
                    f ⊆ count (CARD fs) ∧
                    peval f
                      (CHOICE
                         {phi0 |
                          subst σ phi0 = CHOICE phis ∧ propform phi0 ∧
                          prop_letters phi0 ⊆ count (CARD fs)})})
              (partition (equiv0 (:β)) {phi | IBC phi fs})
              (POW (POW (count (CARD fs))))` by metis_tac[] >>
`FINITE (POW (POW (count (CARD fs))))` suffices_by metis_tac[FINITE_INJ] >>
`FINITE (count (CARD fs))` by metis_tac[FINITE_COUNT] >> 
metis_tac[FINITE_POW]
QED

(*Done with finiteness of IBC*)



val DEG_def =  Define
    `DEG (VAR p) = 0 /\
     DEG (FALSE) = 0 /\
     DEG (NOT form) = DEG form /\
     DEG (DISJ form1 form2) = MAX (DEG form1) (DEG form2) /\
     DEG (DIAM form) = (DEG form) + 1`;



val DEG_IBC_prop_letters = store_thm(
  "DEG_IBC_prop_letters",
  ``∀phi n s.
     DEG phi ≤ n + 1 ∧ (prop_letters phi ⊆ s) ⇔
     IBC phi
     ({VAR v | v ∈ s} ∪
      {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})``,
Induct_on `phi` >> rw[DEG_def]
>- rw[Once IBC_cases,prop_letters_def,SUBSET_DEF] 
>- (`IBC (DISJ phi phi')
         ({VAR v | v ∈ s} ∪
          {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s}) ==>
    (IBC phi
        ({VAR v | v ∈ s} ∪
         {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})) /\ 
    (IBC phi'
        ({VAR v | v ∈ s} ∪
         {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s}))`
       by rw[Once IBC_cases] >>
    `prop_letters (DISJ phi phi') ⊆ s ==>
     prop_letters phi ⊆ s /\ prop_letters phi' ⊆ s` by rw[prop_letters_def] >>
   rw[EQ_IMP_THM] (* 4 *)
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- (fs[prop_letters_def] >> metis_tac[prop_letters_def]))
>- fs[prop_letters_def,Once IBC_cases]
>- (`IBC (¬phi)
         ({VAR v | v ∈ s} ∪
          {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s}) ==>
     IBC phi
         ({VAR v | v ∈ s} ∪
          {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})`
       by rw[Once IBC_cases] >>
   `prop_letters (¬phi) ⊆ s ==> prop_letters phi ⊆ s` by rw[prop_letters_def] >>
   rw[EQ_IMP_THM] (* 3 *)
   >- metis_tac[IBC_cases]
   >- metis_tac[IBC_cases]
   >- (fs[prop_letters_def] >> metis_tac[prop_letters_def]))
>- fs[Once IBC_cases,prop_letters_def]);
 

val DEG_0_propform = store_thm(
"DEG_0_propform",
``!f. DEG f = 0 <=> propform f``,
Induct_on `f` >> fs[DEG_def,propform_def]);

Theorem FINITE_propform_equiv0:
!s. FINITE s ==> 
    FINITE (partition (equiv0 (:β)) 
                      {phi | propform phi /\ prop_letters phi ⊆ s})
Proof
rw[] >>
`FINITE (POW (POW s))` by metis_tac[FINITE_POW] >>
`INJ (\phis. {σ | σ ⊆ s /\ peval σ (CHOICE phis)})
     (partition (equiv0 (:β)) 
                      {phi | propform phi /\ prop_letters phi ⊆ s})
     (POW (POW s))`
  suffices_by metis_tac[FINITE_INJ] >>
rw[INJ_DEF] (* 2 *)
>- rw[POW_DEF,SUBSET_DEF]
>- (irule equiv_on_same_partition >>
   map_every qexists_tac 
   [`equiv0 (:β)`,`{phi | propform phi ∧ prop_letters phi ⊆ s}`,
    `CHOICE phis`,`CHOICE phis'`] >>
   rw[] (* 4 *)
   >- (rw[equiv0_def] >> 
      qabbrev_tac `phi = CHOICE phis` >> 
      qabbrev_tac `phi' = CHOICE phis'` >>
      `phi IN phis /\ phi' IN phis'`
        by
         (`phis <> {} /\ phis' <> {}` 
            suffices_by metis_tac[CHOICE_DEF,Abbr`phi`,Abbr`phi'`] >>
          metis_tac[EMPTY_NOT_IN_partition,equiv0_equiv_on]) >>
      `propform phi /\ propform phi'`
        by
         (fs[partition_def] >> rw[] >> fs[]) >>
      Cases_on `w IN M.frame.world` (*2*)
      >- (drule (peval_satis |> INST_TYPE [alpha |-> ``:'b``]) >> rw[] >>
         `∀M w:β.
             w ∈ M.frame.world ⇒
             (satis M w phi ⇔ peval (λa. w ∈ M.valt a) phi)`
           by metis_tac[peval_satis] >>
         rw[] >> 
         qabbrev_tac `M' = 
                     <| frame := <| world := M.frame.world ;
                                      rel := M.frame.rel; |>;
                         valt := λp w. if p IN s then M.valt p w else F;|>` >>
         `(satis M w phi <=> satis M' w phi) /\
          (satis M w phi' <=> satis M' w phi')`
           by
            (strip_tac >> irule exercise_1_3_1 >> 
            rw[frame_component_equality,Abbr`M'`] >> 
            fs[partition_def] >> rw[] >> fs[SUBSET_DEF,FUN_EQ_THM]) >>
         rw[] >>
         `w IN M'.frame.world` by fs[Abbr`M'`] >>
         `peval (λa. w ∈ M'.valt a) phi ⇔ peval (λa. w ∈ M'.valt a) phi'`
           suffices_by metis_tac[] >>
         fs[EXTENSION] >> 
         `(λa. w ∈ M'.valt a) ⊆ s` suffices_by metis_tac[] >>
         rw[SUBSET_DEF,Abbr`M'`])
      >- metis_tac[satis_in_world])
   >- (`phis <> {}` 
            suffices_by metis_tac[CHOICE_DEF] >>
      metis_tac[EMPTY_NOT_IN_partition,equiv0_equiv_on])
   >- (`phis' <> {}` 
            suffices_by metis_tac[CHOICE_DEF] >>
      metis_tac[EMPTY_NOT_IN_partition,equiv0_equiv_on])
   >- metis_tac[equiv0_equiv_on])
QED

(*needed ?

val partition_eq_EMPTY = store_thm(
  "partition_eq_EMPTY[simp]",
  ``(partition R s = {} <=> s = {}) /\ ({} = partition R s <=> s = {})``,
  conj_tac >> rw[partition_def, Once EXTENSION] >> simp[EXTENSION]);


*)

val equiv0_REFL = store_thm(
  "equiv0_REFL[simp]",
  ``!phi. equiv0 (:β) phi phi``,
  metis_tac[equiv0_def]);

val IBC_SUBSET = store_thm(
    "IBC_SUBSET",
    ``!f fs. IBC f fs ==> !gs. fs SUBSET gs ==> IBC f gs``,
    Induct_on `IBC` >> rw[]
    >> metis_tac[SUBSET_DEF,IBC_cases]);



val IBC_EMPTY = store_thm(
  "IBC_EMPTY",
  ``∀f s. IBC f s ==> s = {} ==> equiv0 (:β) f TRUE \/ equiv0 (:β) f FALSE``,
  Induct_on `IBC` >> rw[] >> fs[equiv0_def,satis_def,TRUE_def]);

val equiv0_TRANS = store_thm(
  "equiv0_TRANS",
  ``!f1 f2 f3. equiv0 (:β) f1 f2 /\ (equiv0 (:β)) f2 f3 ==>(equiv0 (:β)) f1 f3``,
  metis_tac[equiv0_def]);

val equiv0_SYM = store_thm(
  "equiv0_SYM",
  ``!f1 f2. equiv0 (:β) f1 f2 <=> equiv0 (:β) f2 f1``,
  metis_tac[equiv0_def]);


val IBC_CHOICE_equiv0 = store_thm(
  "IBC_CHOICE_equiv0",
  ``!f fs. IBC f fs ==> 
         ?p. IBC p (IMAGE CHOICE (partition (equiv0 (:β)) fs)) /\
                   equiv0 (:β) f p``,
Induct_on `IBC` >> rw[]
>- (`∃p. IBC p (IMAGE CHOICE (partition (equiv0 (:β)) fs)) ∧ 
         equiv0 (:β) f p /\
     ∃p'. IBC p' (IMAGE CHOICE (partition (equiv0 (:β)) fs)) ∧ 
          equiv0 (:β) f' p'` by metis_tac[] >>
   qexists_tac `DISJ p p'` >> rw[]
   >- metis_tac[IBC_cases]
   >- fs[equiv0_def,satis_def])
>- (qexists_tac `FALSE` >> rw[Once IBC_cases])
>- (`∃p. IBC p (IMAGE CHOICE (partition (equiv0 (:β)) fs)) ∧ 
         equiv0 (:β) f p` by metis_tac[] >>
   qexists_tac `¬p` >> rw[Once IBC_cases] >> fs[equiv0_def,satis_def])
>- (fs[partition_def] >>
   qexists_tac `CHOICE {y | y IN fs /\ equiv0 (:β) f y}` >> rw[]
   >- (`(CHOICE {y | y ∈ fs ∧ equiv0 (:β) f y}) IN 
        (IMAGE CHOICE {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 (:β) x y}})`
          by 
           (fs[IMAGE_DEF,PULL_EXISTS] >> qexists_tac `f` >> rw[]) >>
        metis_tac[IBC_cases]) >>
   `{y | y ∈ fs ∧ equiv0 (:β) f y} <> {}` 
     by 
       (`f IN {y | y ∈ fs ∧ equiv0 (:β) f y}` by fs[] >> 
        metis_tac[MEMBER_NOT_EMPTY]) >>
   `(CHOICE {y | y ∈ fs ∧ equiv0 (:β) f y}) IN {y | y ∈ fs ∧ equiv0 (:β) f y}`
     by metis_tac[CHOICE_DEF] >> fs[]));


Theorem FINITE_FINITE_IBC:
!fs. FINITE (partition (equiv0 (:β)) fs) ==>
     FINITE (partition (equiv0 (:β)) {phi | IBC phi fs})
Proof
rw[] >>
`FINITE (IMAGE CHOICE (partition (equiv0 (:β)) fs))` 
  by metis_tac[IMAGE_FINITE] >> 
drule IBC_FINITE_equiv0 >> rw[] >> 
`SURJ (\s. {phi | IBC phi fs /\ !f. f IN s ==> equiv0 (:β) phi f})
      (partition (equiv0 (:β))
             {phi | IBC phi (IMAGE CHOICE (partition (equiv0 (:β)) fs))})
      (partition (equiv0 (:β)) {phi | IBC phi fs})`
  suffices_by metis_tac[FINITE_SURJ] >>
rw[SURJ_DEF] (* 2 *)
>- (rw[partition_def] >> qexists_tac `CHOICE s` >>
   fs[partition_def] >> rw[] (* 2 *)
   >- (`IMAGE CHOICE 
              {t | (∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 (:β) x y})} 
       ⊆ fs`
        by 
         (rw[IMAGE_DEF,SUBSET_DEF] >>
          qmatch_abbrev_tac ‘CHOICE smallset ∈ bigset’ >>
          `smallset <> {}`
            by (simp[Abbr`smallset`, EXTENSION] >> metis_tac[equiv0_REFL]) >>
          ‘smallset ⊆ bigset’
            suffices_by metis_tac[SUBSET_DEF, CHOICE_DEF] >>
          simp[SUBSET_DEF, Abbr`smallset`, Abbr`bigset`]) >>
      irule IBC_SUBSET >> 
      qexists_tac
      `IMAGE CHOICE {t | (∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 (:β) x y})}` >>
      qmatch_abbrev_tac `IBC (CHOICE A) _ /\ _` >> 
      rw[] >> 
      `CHOICE A IN A` suffices_by fs[Abbr`A`] >> 
      `A <> {}` suffices_by metis_tac[CHOICE_DEF] >>
      `x IN A` suffices_by metis_tac[NOT_IN_EMPTY] >> fs[Abbr`A`])
   >- (qabbrev_tac `A = 
                   (IMAGE CHOICE
                   {t | (∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 (:β) x y})})` >>
      simp[EXTENSION] >> rw[] >> 
      `IBC x' fs ==> 
       ((∀f. IBC f A ∧ equiv0 (:β) x f ⇒ equiv0 (:β) x' f) <=> 
        equiv0 (:β) (CHOICE {y | IBC y A ∧ equiv0 (:β) x y}) x')`
        suffices_by metis_tac[] >>
      rw[] >> 
      `(CHOICE {y | IBC y A ∧ equiv0 (:β) x y}) IN 
      {y | IBC y A ∧ equiv0 (:β) x y}` 
       by 
        (`x IN {y | IBC y A ∧ equiv0 (:β) x y}` 
           suffices_by metis_tac[NOT_IN_EMPTY,CHOICE_DEF] >> fs[]) >>
      rw[EQ_IMP_THM] (* 2 *)
      >- (fs[] >> `IBC x A ∧ equiv0 (:β) x x` by fs[] >>
         `equiv0 (:β) x' x` by metis_tac[] >> 
         metis_tac[equiv0_SYM,equiv0_TRANS])
      >- (fs[] >> metis_tac[equiv0_SYM,equiv0_TRANS])))
>- (fs[partition_def] >>
   qabbrev_tac `A = {t | ∃x. x ∈ fs ∧ t = {y | y ∈ fs ∧ equiv0 (:β) x y}}` >>
   simp[PULL_EXISTS] >>
   FREEZE_THEN drule IBC_CHOICE_equiv0 >> rw[] >>   
   qexists_tac `p` >> rw[] (* 2 *)
   >- fs[partition_def,Abbr`A`]
   >- (rw[EXTENSION,EQ_IMP_THM] (* 2 *)
      >- (fs[partition_def,Abbr`A`] >> 
          `equiv0 (:β) x p` by fs[] >>
          metis_tac[equiv0_SYM,equiv0_TRANS])
      >- metis_tac[equiv0_SYM,equiv0_TRANS]))
QED


Theorem prop_2_29_prop_letters:
  !s. FINITE s /\ INFINITE univ(:'b) ==>
      !n. FINITE
             (partition (equiv0 (:β))
                        { f| DEG f <= n /\ prop_letters f ⊆ s})
Proof
gen_tac >> strip_tac >> Induct_on `n` (* 2 *)
>- (`{f | DEG f ≤ 0 ∧ prop_letters f ⊆ s} = 
    {f | propform f ∧ prop_letters f ⊆ s}`
     by (rw[EXTENSION] >> metis_tac[DEG_0_propform]) >> 
    metis_tac[FINITE_propform_equiv0]) >>
rw[ADD1] >> 
`{f | DEG f ≤ n + 1 ∧ prop_letters f ⊆ s} = 
 {phi| IBC phi ({VAR v | v ∈ s} ∪ 
                {◇ psi | DEG psi ≤ n ∧ prop_letters psi ⊆ s})}`
  by 
   (rw[EXTENSION] >> metis_tac[DEG_IBC_prop_letters]) >>
rw[] >> 
irule FINITE_FINITE_IBC >> rw[] >> 



val _ = export_theory();
