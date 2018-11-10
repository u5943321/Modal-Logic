open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

val _ = ParseExtras.tight_equality()

val _ = new_theory "IBCDNFrevised";

(* Basics of equiv *)

val equiv0_def = Define`
     equiv0 (tyi: μ itself) f1 f2 <=> !M w:μ. satis M w f1 <=> satis M w f2`;


val equiv0_equiv_on = store_thm(
  "equiv0_equiv_on",
  ``!s μ. (equiv0 μ) equiv_on s``,
  rw[equiv_on_def] >> metis_tac[equiv0_def]);



val equiv0_TRANS = store_thm(
  "equiv0_TRANS",
  ``!f1 f2 f3 μ. equiv0 μ f1 f2 /\ (equiv0 μ) f2 f3 ==>(equiv0 μ) f1 f3``,
  metis_tac[equiv0_def]);

val equiv0_SYM = store_thm(
  "equiv0_SYM",
  ``!f1 f2 μ. equiv0 μ f1 f2 <=> equiv0 μ f2 f1``,
  metis_tac[equiv0_def]);

val equiv0_REFL = store_thm(
  "equiv0_REFL[simp]",
  ``!f μ. equiv0 μ f f``,
  metis_tac[equiv0_def]);

val equiv0_DISJ_F = store_thm(
  "equiv0_DISJ_F",
  ``equiv0 μ (DISJ FALSE f) f ∧ equiv0 μ (DISJ f FALSE) f``,
  simp[equiv0_def, satis_def]);

val equiv0_TAUT = store_thm(
  "equiv0_TAUT",
  ``equiv0 μ (DISJ p (NOT p)) TRUE ∧ equiv0 μ (DISJ (NOT p) p) TRUE``,
  simp[equiv0_def, satis_def, TRUE_def] >> metis_tac[satis_in_world]);

val equiv0_NOT_NOT = store_thm(
  "equiv0_NOT_NOT",
  ``equiv0 μ (NOT (NOT p)) p``,
  simp[equiv0_def, satis_def] >> metis_tac[satis_in_world]);

(* just AND/absorb/contra *)
val equiv0_demorgan = store_thm(
  "equiv0_demorgan", 
  ``!p q r μ. equiv0 μ (AND p (DISJ q r)) (DISJ (AND p q) (AND p r))``,
  rw[equiv0_def,AND_def,satis_def] >> metis_tac[]);

val equiv0_cancel = store_thm(
  "equiv0_cancel",
  ``!p μ. equiv0 μ (DISJ FALSE p) p``,
  rw[equiv0_def,satis_def]);

val equiv0_contra = store_thm(
  "equiv0_contra",
  ``!p μ. equiv0 μ (AND p (¬p)) FALSE``,
  rw[equiv0_def,AND_def,satis_def] >> metis_tac[]);


val equiv0_absorb = store_thm(
  "equiv0_absorb",
  ``!p μ. equiv0 μ (AND p p) p``,
  rw[equiv0_def,AND_def,satis_def] >> metis_tac[satis_in_world]);


val equiv0_AND_same = store_thm(
"equiv0_AND_same",
``!f1 f2 μ. equiv0 μ (AND f1 f2) (AND (AND f1 f2) f1)``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);



val equiv0_AND_assoc = store_thm(
"equiv0_AND_assoc",
``!f1 f2 f3 μ. equiv0 μ (AND (AND f1 f2) f3) (AND f1 (AND f2 f3))``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);

val equiv0_FALSE = store_thm(
"equiv0_FALSE",
``!f μ. equiv0 μ (AND f FALSE) FALSE``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);



val equiv0_AND_subst = store_thm(
"equiv0_AND_subst",
``!f1 f2 f3 μ. equiv0 μ f1 f2 ==> equiv0 μ (AND f3 f1) (AND f3 f2)``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);


val equiv0_AND_FALSE = store_thm(
"equiv0_AND_FALSE",
``!f μ. equiv0 μ (AND f FALSE) FALSE``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);

val equiv0_AND_SYM = store_thm(
"equiv0_AND_SYM",
``!f1 f2 μ. equiv0 μ (AND f1 f2) (AND f2 f1)``,
rw[equiv0_def,AND_def] >> metis_tac[satis_def]);

val equiv0_IMP_TRUE = store_thm(
"equiv0_IMP_TRUE",
``!f μ. equiv0 μ (IMP f TRUE) TRUE``,
rw[equiv0_def,IMP_def,TRUE_def,satis_def] >> metis_tac[]);

val equiv0_AND_switch = store_thm(
"equiv0_AND_switch",
``!f g h μ. equiv0 μ (AND f (AND g h)) (AND g (AND f h))``,
fs[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]);


val equiv0_IMP = store_thm(
"equiv0_IMP",
``!f g h μ. equiv0 μ (IMP f (AND g h)) (AND (IMP f g) (IMP f h))``,
rw[equiv0_def,AND_def,IMP_def,satis_def] >> metis_tac[]);


val equiv0_IMP_subst = store_thm(
"equiv0_IMP_subst",
``!f g h μ. equiv0 μ g h ==> equiv0 μ (IMP f g) (IMP f h)``,
rw[equiv0_def,AND_def,IMP_def,satis_def] >> metis_tac[]);


val equiv0_IMP_subst2 = store_thm(
"equiv0_IMP_subst2",
``!f g h μ. equiv0 μ g h ==> equiv0 μ (IMP g f) (IMP h f)``,
rw[equiv0_def,AND_def,IMP_def,satis_def] >> metis_tac[]);

val equiv0_AND_subst2 = store_thm(
"equiv0_AND_subst2",
``!f1 f2 f3 μ. equiv0 μ f1 f2 ==> equiv0 μ (AND f1 f3) (AND f2 f3)``,
rw[equiv0_def,AND_def,satis_def] >> metis_tac[]);

val equiv0_AND_IMP = store_thm(
"equiv0_AND_IMP",
``!f g μ. equiv0 μ (IMP (AND f g) f) TRUE``,
rw[equiv0_def,IMP_def,AND_def,TRUE_def,satis_def] >> metis_tac[satis_in_world]);


val equiv0_AND_IMP_CONS = store_thm(
"equiv0_AND_IMP_CONS",
``!f g h μ. equiv0 μ (IMP f g) TRUE ==> equiv0 μ (IMP (AND h f) g) TRUE``,
rw[equiv0_def,IMP_def,AND_def,TRUE_def] >>
eq_tac >> rw[]
>- metis_tac[satis_def]
>- (`satis M w (DISJ (¬f) g)` by metis_tac[] >> metis_tac[satis_def]));


val equiv0_TRUE_absorb = store_thm(
"equiv0_TRUE_absorb",
``!f μ. equiv0 μ (AND TRUE f) f /\ equiv0 μ (AND f TRUE) f``,
rw[satis_def,AND_def,equiv0_def,TRUE_def] >> metis_tac[satis_in_world]);


val equiv0_AND_TRUE = store_thm(
"equiv0_AND_TRUE",
``!f1 f2 μ. equiv0 μ f1 TRUE /\ equiv0 μ f2 TRUE ==> equiv0 μ (AND f1 f2) TRUE``,
rw[equiv0_def,IMP_def,AND_def,TRUE_def] >> metis_tac[satis_def]);


val equiv0_AND_comm_assoc = store_thm(
"equiv0_AND_comm_assoc",
``!f1 f2 f3 μ. equiv0 μ (AND f1 (AND f2 f3)) (AND (AND f1 f3) f2)``,
rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]);

val equiv0_double_IMP = store_thm(
"equiv0_double_IMP",
``!f1 f2 μ. equiv0 μ f1 f2 <=> equiv0 μ (IMP f1 f2) TRUE /\ equiv0 μ (IMP f2 f1) TRUE``,
rw[equiv0_def,IMP_def,TRUE_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_IMP_DISJ_TRUE = store_thm(
"equiv0_IMP_DISJ_TRUE",
``!f g h μ. equiv0 μ (IMP f h) TRUE /\ equiv0 μ (IMP g h) TRUE ==> equiv0 μ (IMP (DISJ f g) h) TRUE``,
rw[IMP_def,equiv0_def,satis_def,TRUE_def] >> metis_tac[satis_in_world]);


val equiv0_IMP_REFL = store_thm(
"equiv0_IMP_REFL",
``!f μ. equiv0 μ (IMP f f) TRUE``,
rw[IMP_def,equiv0_def,satis_def,TRUE_def] >> metis_tac[satis_in_world]);






(* basics of CONJ *)

val (CONJ_OF_rules, CONJ_OF_ind, CONJ_OF_cases) = Hol_reln`
(!c0 c. (c = c0 \/ c = ¬c0) ==> CONJ_OF c {c0}) /\
(!f0 f1 f2 fs. (f1 = f0 \/ f1 = ¬f0) /\ f0 IN fs /\ CONJ_OF f2 (fs DELETE f0) ==> CONJ_OF (AND f1 f2) fs)`;

val CONJ_OF_FINITE = store_thm(
"CONJ_OF_FINITE",
``!f s. CONJ_OF f s ==> FINITE s /\ s <> {}``,
Induct_on `CONJ_OF` >> rw[] >> strip_tac >> fs[]
);

val lemma_AND = Q.prove(
  `{ AND d f | f | CONJ_OF f s } = IMAGE (\f. AND d f) {f | CONJ_OF f s}`,
  simp[EXTENSION]);

val AND_INJ = store_thm(
"AND_INJ[simp]",
``!f1 f2 g1 g2. AND f1 f2 = AND g1 g2 <=> f1 = g1 /\ f2 = g2``,
simp[AND_def]);

val FINITE_CONJ_OF = store_thm(
"FINITE_CONJ_OF",
``!s. FINITE s ==> FINITE {f | CONJ_OF f s}``,
  ho_match_mp_tac FINITE_COMPLETE_INDUCTION >> rw[] >>
  ONCE_REWRITE_TAC [CONJ_OF_cases] >> dsimp[] >>
  Cases_on `s = {}` >> simp[GSPEC_OR] >> rw[] 
  >- (Cases_on `?f. s = {f}` >> fs[])
  >- (Cases_on `?f. s = {f}` >> fs[])
  >- (qmatch_abbrev_tac `FINITE bigset` >>
  `bigset =
    BIGUNION (IMAGE (λd. {AND d f | f | CONJ_OF f (s DELETE d)}) s)`
        by (simp[Once EXTENSION, Abbr`bigset`] >> dsimp[] >> metis_tac[]) >>
  simp[PULL_EXISTS,lemma_AND] >> rw[] >>
  first_x_assum irule >> simp[PSUBSET_DEF, EXTENSION] >> metis_tac[])
  >- (qmatch_abbrev_tac `FINITE bigset` >>
  `bigset =
    BIGUNION (IMAGE (λd. {AND (¬d) f | f | CONJ_OF f (s DELETE d)}) s)`
        by (simp[Once EXTENSION, Abbr`bigset`] >> dsimp[] >> metis_tac[]) >>
  simp[PULL_EXISTS,lemma_AND] >> rw[] >>
  first_x_assum irule >> simp[PSUBSET_DEF, EXTENSION] >> metis_tac[])
  );




val CONJ_OF_equiv0 = store_thm(
"CONJ_OF_equiv0",
``!f fs. CONJ_OF f fs ==> !g. g IN fs ==> equiv0 μ (AND f g) FALSE \/ equiv0 μ (AND f g) f``,
Induct_on `CONJ_OF` >> rw[]
>- rw[equiv0_absorb]
>- metis_tac[equiv0_contra,equiv0_AND_SYM,equiv0_TRANS,equiv0_SYM]
>- (Cases_on `g = f0`
   >- (`equiv0 μ (AND (AND f0 f) g) (AND f0 f)` suffices_by metis_tac[] >> rw[] >> metis_tac[equiv0_AND_same,equiv0_SYM])
   >- (`equiv0 μ (AND f g) ⊥ ∨ equiv0 μ (AND f g) f` by metis_tac[]
      >- (`equiv0 μ (AND (AND f0 f) g) (AND f0 (AND f g))` by metis_tac[equiv0_AND_assoc] >>
         `equiv0 μ (AND f0 (AND f g)) (AND f0 FALSE)` by metis_tac[equiv0_AND_subst] >>
         `equiv0 μ (AND f0 FALSE) FALSE` by metis_tac[equiv0_AND_FALSE] >>
         metis_tac[equiv0_TRANS,equiv0_SYM])
      >- (`equiv0 μ (AND (AND f0 f) g) (AND f0 (AND f g))` by metis_tac[equiv0_AND_assoc] >>
         `equiv0 μ (AND f0 (AND f g)) (AND f0 f)` by metis_tac[equiv0_AND_subst] >>
         metis_tac[equiv0_TRANS,equiv0_SYM])))
>- (Cases_on `g = f0`
   >- (`equiv0 μ (AND (AND (¬f0) f) g) FALSE` suffices_by metis_tac[] >> rw[] >>
      `equiv0 μ (AND (AND (¬f0) f) f0) (AND f0 (AND (¬f0) f))` by metis_tac[equiv0_AND_SYM] >>
      `equiv0 μ (AND f0 (AND (¬f0) f)) (AND (AND f0 (¬f0)) f)` by metis_tac[equiv0_AND_assoc,equiv0_SYM] >>
      `equiv0 μ (AND (AND f0 (¬f0)) f) (AND f (AND f0 (¬f0)))` by metis_tac[equiv0_AND_SYM] >>
      `equiv0 μ (AND f (AND f0 (¬f0))) (AND f FALSE)` by metis_tac[equiv0_AND_subst,equiv0_contra] >> metis_tac[equiv0_TRANS,equiv0_AND_FALSE])
   >- (`equiv0 μ (AND f g) ⊥ ∨ equiv0 μ (AND f g) f` by metis_tac[]
      >- (`equiv0 μ (AND (AND (¬f0) f) g) (AND (¬f0) (AND f g))` by metis_tac[equiv0_AND_assoc] >>
         `equiv0 μ (AND (¬f0) (AND f g)) (AND (¬f0) FALSE)` by metis_tac[equiv0_AND_subst] >>
         `equiv0 μ (AND (¬f0) FALSE) FALSE` by metis_tac[equiv0_AND_FALSE] >>
         metis_tac[equiv0_TRANS,equiv0_SYM])
      >- (`equiv0 μ (AND (AND (¬f0) f) g) (AND (¬f0) (AND f g))` by metis_tac[equiv0_AND_assoc] >>
         `equiv0 μ (AND (¬f0) (AND f g)) (AND (¬f0) f)` by metis_tac[equiv0_AND_subst] >>
         metis_tac[equiv0_TRANS,equiv0_SYM]))));



(* basics of lit list *)

val negf_def = Define`
negf (f:'a form,T) = f /\
negf (f,F) = ¬f`;

val _= export_rewrites ["negf_def"]

val lit_list_to_form_def = Define`
lit_list_to_form [] = TRUE /\
lit_list_to_form [fb] = negf fb /\
lit_list_to_form (fb :: rest) = AND (negf fb) (lit_list_to_form rest)`;

val _= export_rewrites ["lit_list_to_form_def"]

val lneg_def = Define`
lneg (f,T) = (f, F) /\ lneg (f, F) = (f, T)`;

val lneg_applied = store_thm(
"lneg_applied",
``!fb. equiv0 μ (negf (lneg fb)) (¬(negf fb))``,
Cases_on `fb` >> Cases_on `r`
>- simp[lneg_def] >- simp[lneg_def,equiv0_NOT_NOT,equiv0_SYM]);

val lneg_thm = store_thm(
"lneg_thm",
``lneg (p, b) = (p, ¬b)``,
Cases_on `b` >> rw[lneg_def]);

val CONJ_OF_AND_lemma = store_thm(
"CONJ_OF_AND_lemma",
``!f fs. CONJ_OF f fs ==> ?l. set (MAP FST l) = fs /\ ALL_DISTINCT (MAP FST l) /\ f = lit_list_to_form l``,
Induct_on `CONJ_OF` >> rw[]
>- (qexists_tac `[(c0,T)]` >> simp[])
>- (qexists_tac `[(c0,F)]` >> simp[])
>- (qexists_tac `CONS (f0,T) l` >> simp[] >>
   `fs DELETE f0 <> {}`  by metis_tac[CONJ_OF_FINITE] >>
   `?h t. l = h :: t` by (Cases_on `l` >> fs[]) >>
   simp[])
>- (qexists_tac `CONS (f0,F) l` >> simp[] >>
   `fs DELETE f0 <> {}`  by metis_tac[CONJ_OF_FINITE] >>
   `?h t. l = h :: t` by (Cases_on `l` >> fs[]) >>
   simp[]));


val CONJ_OF_AND_lemma_nonempty = store_thm(
"CONJ_OF_AND_lemma_nonempty",
``!f fs. CONJ_OF f fs ==> ?l. set (MAP FST l) = fs /\ l <> [] /\ ALL_DISTINCT (MAP FST l) /\ f = lit_list_to_form l``,
rw[] >> `?l. set (MAP FST l) = fs /\ ALL_DISTINCT (MAP FST l) /\ f = lit_list_to_form l` by metis_tac[CONJ_OF_AND_lemma] >> qexists_tac `l` >> rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> `set (MAP FST l) = {}` by fs[] >> metis_tac[CONJ_OF_FINITE]);


val list_to_CONJ_OF = store_thm(
"list_to_CONJ_OF",
``!l fs. l <> [] ==> set (MAP FST l) = fs /\ ALL_DISTINCT (MAP FST l) ==> CONJ_OF (lit_list_to_form l) fs``,
Induct_on `l` >> rw[] >>
Cases_on `l`
>- (rw[] >>
   `negf h = FST h \/ negf h = (¬(FST h))` by (Cases_on `h` >> Cases_on `r` >> simp[negf_def]) >>
   metis_tac[CONJ_OF_cases])
>- (`h' :: t <> []` by fs[] >>
   `CONJ_OF (lit_list_to_form (h'::t)) (set (MAP FST (h'::t)))` by metis_tac[] >>
   rw[lit_list_to_form_def] >>
   `¬MEM (FST h') (MAP FST t) ∧ ALL_DISTINCT (MAP FST t)` by fs[] >>
   `CONJ_OF (lit_list_to_form (h'::t)) (FST h' INSERT set (MAP FST t))` by metis_tac[] >>
   rw[Once CONJ_OF_cases] >>
   `∃f0.
   (negf h = f0 ∨ negf h = ¬f0) ∧
   (f0 = FST h ∨ f0 = FST h' ∨ MEM f0 (MAP FST t)) ∧
   CONJ_OF (lit_list_to_form (h'::t))
     ((FST h INSERT FST h' INSERT set (MAP FST t)) DELETE f0)` suffices_by metis_tac[] >>
   qexists_tac `FST h` >> rw[]
   >- (Cases_on `h` >> Cases_on `r` >> rw[negf_def])
   >- (`((FST h INSERT FST h' INSERT set (MAP FST t)) DELETE FST h) = (FST h' INSERT set (MAP FST t))` by (fs[INSERT_DEF,DELETE_DEF,EXTENSION] >> metis_tac[]) >> metis_tac[])));
   


val lit_list_to_form_APPEND= store_thm(
"lit_list_to_form_APPEND",
``!l1 l2. equiv0 μ (AND (lit_list_to_form l1) (lit_list_to_form l2)) (lit_list_to_form (l1 ++ l2))``,
Induct_on `l1` >> simp[]
>- metis_tac[equiv0_TRUE_absorb]
>- (Cases_on `l1` >> simp[]
   >- (Cases_on `l2` >> simp[] >> metis_tac[equiv0_TRUE_absorb])
   >- (rw[] >>
      `equiv0 μ (AND (AND (negf h') (lit_list_to_form (h::t))) (lit_list_to_form l2)) (AND (negf h') (AND (lit_list_to_form (h::t)) (lit_list_to_form l2)))` by metis_tac[equiv0_AND_assoc] >>
      `equiv0 μ (AND (negf h') (AND (lit_list_to_form (h::t)) (lit_list_to_form l2))) (AND (negf h') (lit_list_to_form (h::(t ⧺ l2))))` suffices_by metis_tac[equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (AND (lit_list_to_form (h::t)) (lit_list_to_form l2)) (lit_list_to_form (h::t ⧺ l2))` by metis_tac[] >>
      irule equiv0_AND_subst >>
      `h :: (t ++ l2) = h :: t ++ l2` by simp[] >> metis_tac[])));

val neg_AND_FALSE = store_thm(
"neg_AND_FALSE",
``!fb l. MEM (lneg fb) l ==> equiv0 μ (AND (negf fb) (lit_list_to_form l)) FALSE``,
Induct_on `l` >> simp[] >> rw[]
>- (Cases_on `l`
   >- (simp[] >>
      `equiv0 μ (negf (lneg fb)) (¬(negf fb))` by metis_tac[lneg_applied] >>
      `equiv0 μ (AND (negf fb) (negf (lneg fb))) (AND (negf fb) (¬negf fb))` by simp[equiv0_AND_subst] >>
      `equiv0 μ (AND (negf fb) (¬negf fb)) FALSE` by metis_tac[equiv0_contra] >>
      metis_tac[equiv0_TRANS])
   >- (simp[] >>
      `equiv0 μ (AND (negf fb) (AND (negf (lneg fb)) (lit_list_to_form (h::t))))
      (AND (AND (negf fb) (negf (lneg fb))) (lit_list_to_form (h::t)))` by metis_tac[equiv0_AND_assoc,equiv0_SYM] >>
      `equiv0 μ (negf (lneg fb)) (¬(negf fb))` by metis_tac[lneg_applied] >>
      `equiv0 μ (AND (negf fb) (negf (lneg fb))) (AND (negf fb) (¬(negf fb)))` by metis_tac[equiv0_AND_subst] >>
      `equiv0 μ (AND (negf fb) (negf (lneg fb))) FALSE` by metis_tac[equiv0_contra,equiv0_TRANS] >>
      `equiv0 μ (AND (AND (negf fb) (negf (lneg fb))) (lit_list_to_form (h::t))) (AND FALSE (lit_list_to_form (h::t)))` by metis_tac[equiv0_AND_SYM,equiv0_AND_subst,equiv0_TRANS] >>
      `equiv0 μ (AND ⊥ (lit_list_to_form (h::t))) FALSE` by metis_tac[equiv0_AND_SYM,equiv0_TRANS,equiv0_FALSE] >> metis_tac[equiv0_TRANS]))
>- (Cases_on `l` >> fs[] >>
      `equiv0 μ (AND (negf fb) (lit_list_to_form (h'::t))) ⊥` by metis_tac[] >>
      `equiv0 μ (AND (negf h) (lit_list_to_form (h'::t))) (AND (lit_list_to_form (h'::t)) (negf h))` by metis_tac[equiv0_AND_SYM] >>
      `equiv0 μ (AND (negf fb) (AND (negf h) (lit_list_to_form (h'::t)))) (AND (negf fb) (AND (lit_list_to_form (h'::t)) (negf h)))` by metis_tac[equiv0_AND_subst] >>
      `equiv0 μ (AND (negf fb) (AND (lit_list_to_form (h'::t)) (negf h)))
      (AND (AND (negf fb) (lit_list_to_form (h'::t))) (negf h))` by metis_tac[equiv0_AND_assoc,equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (AND (AND (negf fb) (lit_list_to_form (h'::t))) (negf h)) (AND FALSE (negf h))` by metis_tac[equiv0_AND_subst,equiv0_AND_SYM,equiv0_SYM,equiv0_TRANS] >>
      `equiv0 μ (AND FALSE (negf h)) FALSE` by metis_tac[equiv0_SYM,equiv0_TRANS,equiv0_AND_SYM,equiv0_FALSE] >> metis_tac[equiv0_TRANS]));

val MEM_equiv0_AND = store_thm(
"MEM_equiv0_AND",
``!fb l. MEM fb l ==> equiv0 μ (AND (negf fb) (lit_list_to_form l)) (lit_list_to_form l)``,
Induct_on `l` >> simp[] >> rw[]
>- (Cases_on `l` >> simp[]
   >- metis_tac[equiv0_absorb]
   >- (`equiv0 μ (AND (negf fb) (AND (negf fb) (lit_list_to_form (h::t))))
      (AND (AND (negf fb) (negf fb)) (lit_list_to_form (h::t)))` by metis_tac[equiv0_AND_assoc,equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (AND (negf fb) (negf fb)) (negf fb)` by metis_tac[equiv0_absorb] >>
      `equiv0 μ (AND (AND (negf fb) (negf fb)) (lit_list_to_form (h::t)))
      (AND (negf fb) (lit_list_to_form (h::t)))` by metis_tac[equiv0_AND_subst,equiv0_AND_SYM,equiv0_TRANS,equiv0_SYM] >> metis_tac[equiv0_TRANS]))
>- (Cases_on `l` >> simp[]
   >- fs[]
   >- (`equiv0 μ (AND (negf fb) (lit_list_to_form (h'::t))) (lit_list_to_form (h'::t))` by metis_tac[] >>
      `equiv0 μ (AND (negf h) (lit_list_to_form (h'::t)))
       (AND (lit_list_to_form (h'::t)) (negf h))` by metis_tac[equiv0_AND_SYM] >>
      `equiv0 μ (AND (negf fb) (AND (negf h) (lit_list_to_form (h'::t))))
       (AND (negf fb) (AND (lit_list_to_form (h'::t)) (negf h)))` by metis_tac[equiv0_AND_subst,equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (AND (negf fb) (AND (lit_list_to_form (h'::t)) (negf h)))
       (AND (AND (negf fb) (lit_list_to_form (h'::t))) (negf h))` by metis_tac[equiv0_AND_assoc,equiv0_AND_SYM,equiv0_SYM,equiv0_TRANS] >>
      `equiv0 μ (AND (AND (negf fb) (lit_list_to_form (h'::t))) (negf h))
      (AND (lit_list_to_form (h'::t)) (negf h))` by metis_tac[equiv0_AND_subst,equiv0_AND_SYM,equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (AND (lit_list_to_form (h'::t)) (negf h)) (AND (negf h) (lit_list_to_form (h'::t)))` by metis_tac[equiv0_AND_SYM] >> metis_tac[equiv0_TRANS])));

val lit_list_to_form_CONS = store_thm(
"lit_list_to_form_CONS",
``!h l. equiv0 μ (lit_list_to_form (h :: l)) (AND (negf h) (lit_list_to_form l))``,
Cases_on `l` >> simp[] >> rw[] >> rw[AND_def,equiv0_def,satis_def,TRUE_def] >> metis_tac[satis_in_world]);

val lit_list_to_form_lneg = store_thm(
"lit_list_to_form_lneg",
``!f l1 l2. MEM f l1 /\ MEM (lneg f) l2 ==> equiv0 μ (lit_list_to_form (l1 ++ l2)) FALSE``,
Induct_on `l1` >> simp[] >> rw[]
>- (`equiv0 μ (lit_list_to_form (f::(l1 ⧺ l2))) (AND (negf f) (lit_list_to_form (l1 ++ l2)))` by simp[lit_list_to_form_CONS] >>
   `MEM (lneg f) (l1 ++ l2)` by simp[] >>
   `equiv0 μ (AND (negf f) (lit_list_to_form (l1 ⧺ l2))) FALSE` by metis_tac[neg_AND_FALSE] >>
   metis_tac[equiv0_TRANS])
>- (`equiv0 μ (lit_list_to_form (h::(l1 ⧺ l2))) (AND (negf h) (lit_list_to_form (l1 ++ l2)))` by fs[lit_list_to_form_CONS] >> first_x_assum drule_all >> rw[] >>
   `equiv0 μ (AND (negf h) FALSE) FALSE` by metis_tac[equiv0_AND_FALSE] >>
   metis_tac[equiv0_AND_subst,equiv0_TRANS,equiv0_SYM]));

val lit_list_to_form_IMP_CONS = store_thm(
"lit_list_to_form_IMP_CONS",
``equiv0 μ (IMP P (lit_list_to_form (h :: l))) (AND (IMP P (lit_list_to_form [h])) (IMP P (lit_list_to_form l)))``,
`equiv0 μ (lit_list_to_form (h :: l)) (AND (negf h) (lit_list_to_form l))` by metis_tac[lit_list_to_form_CONS] >>
`equiv0 μ (lit_list_to_form [h]) (negf h)` by simp[] >>
`equiv0 μ (P -> lit_list_to_form [h]) (P -> (negf h))` by metis_tac[equiv0_IMP_subst] >>
`equiv0 μ (AND (P -> lit_list_to_form [h]) (P -> lit_list_to_form l))
(AND (P -> (negf h)) (P -> lit_list_to_form l))` by metis_tac[equiv0_AND_subst2] >>
`equiv0 μ (P -> lit_list_to_form (h::l)) (P -> (AND (negf h) (lit_list_to_form l)))` by metis_tac[equiv0_IMP_subst] >>
`equiv0 μ (P -> AND (negf h) (lit_list_to_form l)) (AND (P -> negf h) (P -> lit_list_to_form l))` by metis_tac[equiv0_IMP] >>
metis_tac[equiv0_SYM,equiv0_TRANS]);

val MEM_equiv0_TRUE = store_thm(
"MEM_equiv0_TRUE",
``MEM h l ==> equiv0 μ (IMP (lit_list_to_form l) (lit_list_to_form [h])) TRUE``,
Induct_on `l` >> simp[] >> rw[]
>- (`equiv0 μ (lit_list_to_form (h::l)) (AND (negf h) (lit_list_to_form l))` by metis_tac[lit_list_to_form_CONS] >>
   `equiv0 μ (lit_list_to_form (h::l) -> negf h)
    ((AND (negf h) (lit_list_to_form l)) -> negf h)` by metis_tac[equiv0_IMP_subst2] >>
   metis_tac[equiv0_TRANS,equiv0_SYM,equiv0_AND_IMP])
>- (`equiv0 μ (lit_list_to_form (h'::l)) (AND (negf h') (lit_list_to_form l))` by metis_tac[lit_list_to_form_CONS] >>
   `equiv0 μ ((AND (negf h') (lit_list_to_form l)) -> negf h) TRUE` suffices_by metis_tac[equiv0_SYM,equiv0_TRANS,equiv0_IMP_subst2] >>
   `lit_list_to_form [h] = negf h` by fs[] >>
   fs[] >> metis_tac[equiv0_AND_IMP_CONS]));

val lit_list_to_form_SUBSET = store_thm(
"lit_list_to_form_SUBSET",
``!l1 l2. (set l1) SUBSET (set l2) ==> equiv0 μ (IMP (lit_list_to_form l2) (lit_list_to_form l1)) TRUE``,
Induct_on `l1` >> simp[] >> rw[]
>- metis_tac[equiv0_IMP_TRUE]
>- (`equiv0 μ (lit_list_to_form l2 -> lit_list_to_form l1) TRUE` by metis_tac[] >>
   `equiv0 μ (IMP (lit_list_to_form l2) (lit_list_to_form [h])) TRUE` by metis_tac[MEM_equiv0_TRUE] >>
   `equiv0 μ (lit_list_to_form l2 -> lit_list_to_form (h::l1))
    (AND (IMP (lit_list_to_form l2) (lit_list_to_form [h])) (IMP (lit_list_to_form l2) (lit_list_to_form l1)))` by metis_tac[lit_list_to_form_IMP_CONS] >>
   `equiv0 μ (AND (lit_list_to_form l2 -> lit_list_to_form [h])
                (lit_list_to_form l2 -> lit_list_to_form l1)) TRUE` by metis_tac[equiv0_AND_TRUE] >> metis_tac[equiv0_TRANS]));

val lit_list_to_form_SYM = store_thm(
"lit_list_to_form_SYM",
``!l1 l2. set l1 = set l2 ==> equiv0 μ (lit_list_to_form l1) (lit_list_to_form l2)``,
rw[] >>
`(set l1) SUBSET (set l2) /\ (set l2) SUBSET (set l1)` by metis_tac[SET_EQ_SUBSET] >>
`equiv0 μ (IMP (lit_list_to_form l2) (lit_list_to_form l1)) TRUE /\
 equiv0 μ (IMP (lit_list_to_form l1) (lit_list_to_form l2)) TRUE` by metis_tac[lit_list_to_form_SUBSET] >> metis_tac[equiv0_double_IMP]);

val opposite_polarity_EXIST = store_thm(
"opposite_polarity_EXIST",
``!l1 l2. set (MAP FST l1) = set (MAP FST l2) /\ set l1 <> set l2 ==> ?fb. MEM fb l1 /\ MEM (lneg fb) l2``,
simp[EXTENSION,MEM_MAP,EXISTS_PROD,lneg_thm] >> rw[] >>
rename [`MEM (l,b) l1 <> _`] >>
Cases_on `MEM (l,b) l1`
>- (qexists_tac `l` >> qexists_tac `b` >>
   `?p. MEM (l, p) l2` by metis_tac[] >> 
   Cases_on `b = p` >> fs[] >> `p = ¬b` by metis_tac[] >> fs[])
>- (fs[] >>
   qexists_tac `l` >> qexists_tac `¬b` >>
   `?p. MEM (l, p) l1` by metis_tac[] >> 
   Cases_on `b = p` >> fs[] >> `p = ¬b` by metis_tac[] >> fs[]));

val EQ_MAP_FST_equiv0_cases = store_thm(
"EQ_MAP_FST_equiv0_cases",
``!l1 l2. set (MAP FST l1) = set (MAP FST l2) ==>
equiv0 μ (lit_list_to_form (l1 ++ l2)) FALSE \/ equiv0 μ (lit_list_to_form (l1 ++ l2)) (lit_list_to_form l1)``,
rw[] >> Cases_on `set l1 = set l2`
>- (`equiv0 μ (lit_list_to_form (l1 ⧺ l2)) (AND (lit_list_to_form l1) (lit_list_to_form l2))` by metis_tac[lit_list_to_form_APPEND,equiv0_SYM] >> drule lit_list_to_form_SYM >> rw[] >>
   `equiv0 μ (AND (lit_list_to_form l1) (lit_list_to_form l2)) (AND (lit_list_to_form l1) (lit_list_to_form l1))` by metis_tac[equiv0_AND_subst,equiv0_SYM] >>
   `equiv0 μ (AND (lit_list_to_form l1) (lit_list_to_form l1)) (lit_list_to_form l1)` by metis_tac[equiv0_absorb] >>
   metis_tac[equiv0_TRANS])
>- metis_tac[opposite_polarity_EXIST,lit_list_to_form_lneg]);



(* basics of IBC *)

val (IBC_rules, IBC_ind, IBC_cases) = Hol_reln`
(!f1 f2 s.
IBC f1 s /\ IBC f2 s ==> IBC (DISJ f1 f2) s) /\
(!s. IBC FALSE s) /\
(!f s. IBC f s ==> IBC (NOT f) s) /\
(!f s. f IN s ==> IBC f s)`;

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 2100,
                  pp_elements = [TOK "//e"],
                  term_name = "part_equiv0"}
val _ = overload_on ("part_equiv0", ``partition (equiv0 μ)``)   

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix(NONASSOC, 1900),
                  pp_elements = [TOK "//E", BreakSpace(1,0)],
                  term_name = "part_equiv"}
val _ = overload_on ("part_equiv", ``\s tyi. partition (equiv0 tyi) s``);

(* basics of DISJ *)

val SING_INSERT_11 = store_thm(
  "SING_INSERT_11",
  ``x NOTIN xs ==> ({e} = x INSERT xs <=> e = x /\ xs = {})``,
  strip_tac >> simp[EQ_IMP_THM] >> simp[EXTENSION] >> metis_tac[]);

val (DISJ_OF0_rules, DISJ_OF0_ind, DISJ_OF0_cases) = Hol_reln`
(!f fs. f IN fs ==> DISJ_OF0 f fs) /\
(!f1 f2 fs. f1 IN fs /\ DISJ_OF0 f2 (fs DELETE f1) ==> DISJ_OF0 (DISJ f1 f2) fs)
`;

val lemma = Q.prove(
  `{ DISJ d f | f | DISJ_OF0 f s } = IMAGE (\f. DISJ d f) { f | DISJ_OF0 f s}`,
  simp[EXTENSION]);


val FINITE_DISJ_OF0 = store_thm(
"FINITE_DISJ_OF0",
``!s. FINITE s ==> FINITE {f | DISJ_OF0 f s}``,
  ho_match_mp_tac FINITE_COMPLETE_INDUCTION >> rw[] >>
  ONCE_REWRITE_TAC [DISJ_OF0_cases] >> dsimp[] >>
  Cases_on `s = {}` >> simp[GSPEC_OR] >>
  qmatch_abbrev_tac `FINITE bigset` >>
  `bigset =
    BIGUNION (IMAGE (λd. {DISJ d f | f | DISJ_OF0 f (s DELETE d)}) s)`
        by (simp[Once EXTENSION, Abbr`bigset`] >> dsimp[] >> metis_tac[]) >>
  simp[] >> simp[PULL_EXISTS] >> simp[lemma] >> rw[] >>
  first_x_assum irule >> simp[PSUBSET_DEF, EXTENSION] >> metis_tac[]);

val DISJ_OF_def = Define`
DISJ_OF f fs <=> f = FALSE \/ DISJ_OF0 f fs`;

val lemma_FINITE = Q.prove(
  `FINITE s ==> FINITE {f | DISJ_OF f s}`,
  simp[DISJ_OF_def,GSPEC_OR] >> metis_tac[FINITE_DISJ_OF0]);


(* lit_list_to_form DISJ version *)

val equiv0_DISJ_subst = store_thm(
"equiv0_DISJ_subst",
``!f g h μ. equiv0 μ f g ==> equiv0 μ (DISJ h f) (DISJ h g)``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val lit_list_to_form2_def = Define`
lit_list_to_form2 [] = FALSE /\
lit_list_to_form2 [fb] = fb /\
lit_list_to_form2 (fb :: rest) = DISJ fb (lit_list_to_form2 rest)`;

val _= export_rewrites ["lit_list_to_form2_def"]

val lit_list_to_form2_CONS = store_thm(
"lit_list_to_form2_CONS",
``!h l. equiv0 μ (lit_list_to_form2 (h :: l)) (DISJ h (lit_list_to_form2 l))``,
Cases_on `l` >> simp[] >> rw[] >> rw[equiv0_def,satis_def]);

val DISJ_OF0_DISJ_lemma = store_thm(
"DISJ_OF0_DISJ_lemma",
``!f fs. DISJ_OF0 f fs ==> ?l. set l SUBSET fs /\ equiv0 μ f (lit_list_to_form2 l)``,
Induct_on `DISJ_OF0` >> rw[]
>- (qexists_tac `[f]` >> simp[])
>- (qexists_tac `CONS f1 l` >> simp[] >>
   fs[Once DISJ_OF0_cases]
   >- (rw[lit_list_to_form2_def] >>
      `(fs DELETE f1) SUBSET fs` by simp[DELETE_DEF,SUBSET_DEF] >> fs[SUBSET_DEF] >>
      `equiv0 μ (lit_list_to_form2 (f1::l)) (DISJ f1 (lit_list_to_form2 l))` by rw[lit_list_to_form2_CONS] >>
      metis_tac[equiv0_DISJ_subst,equiv0_TRANS,equiv0_SYM])
   >- (rw[]
      >- (`(fs DELETE f1) SUBSET fs` by simp[DELETE_DEF,SUBSET_DEF] >> fs[SUBSET_DEF])
      >- (`equiv0 μ (lit_list_to_form2 (f1::l)) (DISJ f1 (lit_list_to_form2 l))` by rw[lit_list_to_form2_CONS] >>
         `equiv0 μ (DISJ f1 (lit_list_to_form2 l)) (DISJ f1 (DISJ f1' f2))` by metis_tac[equiv0_DISJ_subst,equiv0_SYM] >>
         metis_tac[equiv0_SYM,equiv0_TRANS]))));

val DISJ_OF0_DISJ_lemma_EQ = store_thm(
"DISJ_OF0_DISJ_lemma_EQ",
``!f fs. DISJ_OF0 f fs ==>  ?l. l <> [] /\ (set l) SUBSET fs /\ f = (lit_list_to_form2 l) /\ ALL_DISTINCT l``,
Induct_on `DISJ_OF0` >> rw[]
>- (qexists_tac `[f]` >> rw[])
>- (qexists_tac `f1 :: l` >> rw[]
   >- fs[SUBSET_DEF]
   >- (Cases_on `l` >- metis_tac[]
      >- fs[lit_list_to_form2_def])
   >- (fs[SUBSET_DEF] >> SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[])
));


val DISJ_OF0_SUBSET = store_thm(
"DISJ_OF0_SUBSET",
``!f fs. DISJ_OF0 f fs ==> !gs. fs SUBSET gs ==> DISJ_OF0 f gs``,
Induct_on `DISJ_OF0` >> rw[]
>- fs[Once DISJ_OF0_cases,SUBSET_DEF]
>- (`(fs DELETE f1) SUBSET (gs DELETE f1)` by fs[SUBSET_DEF] >>
   `DISJ_OF0 f (gs DELETE f1)` by metis_tac[] >>
   `f1 IN gs` by fs[SUBSET_DEF] >> metis_tac[DISJ_OF0_cases]));

val list_to_DISJ_OF0_lemma = store_thm(
"list_to_DISJ_OF0_lemma",
``!l. l <> [] /\ ALL_DISTINCT l ==> DISJ_OF0 (lit_list_to_form2 l) (set l)``,
Induct_on `l` >> rw[] >>
Cases_on `l` >> rw[] >- (`h IN {h}` by simp[] >> metis_tac[DISJ_OF0_cases])
>- (rw[Once DISJ_OF0_cases] >>
   `¬MEM h' t ∧ ALL_DISTINCT t` by fs[] >>
   `DISJ_OF0 (lit_list_to_form2 (h'::t)) (h' INSERT set t)` by metis_tac[] >>
   `((h INSERT h' INSERT set t) DELETE h) = (h' INSERT set t)` by (fs[DELETE_DEF,INSERT_DEF,EXTENSION] >> metis_tac[]) >>
   metis_tac[]));

val list_to_DISJ_OF0 = store_thm(
"list_to_DISJ_OF0",
``!l fs. l <> [] /\ (set l) SUBSET fs /\ ALL_DISTINCT l ==> DISJ_OF0 (lit_list_to_form2 l) fs``,
rw[] >> metis_tac[list_to_DISJ_OF0_lemma,DISJ_OF0_SUBSET]);
   
   



(* basics of DNF *)

val equiv0_DISJ_absorb = store_thm(
"equiv0_DISJ_absorb",
``!f μ. equiv0 μ f (DISJ f f)``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_DISJ_absorb = store_thm(
"equiv0_DISJ_DISJ_absorb",
``!f g μ. equiv0 μ (DISJ f g) (DISJ f (DISJ f g))``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_comm_assoc = store_thm(
"equiv0_DISJ_COMM_ASSOC",
``!f g h μ. equiv0 μ (DISJ f (DISJ g h)) (DISJ g (DISJ f h))``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_assoc = store_thm(
"equiv0_DISJ_ASSOC",
``!f g h μ. equiv0 μ (DISJ (DISJ f g) h) (DISJ f (DISJ g h))``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_FALSE = store_thm(
"equiv0_DISJ_FALSE",
``!f t μ. equiv0 μ f (DISJ t FALSE) ==> equiv0 μ f t``,
rw[equiv0_def,satis_def]);

val equiv0_DISJ_double_subst = store_thm(
"equiv0_DISJ_double_subst",
``!a b c d. equiv0 μ a b /\ equiv0 μ c d ==> equiv0 μ (DISJ a c) (DISJ b d)``,
rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);
  
   

val equiv0_TRUE_absorb = store_thm(
"equiv0_TRUE_absorb",
``!f. equiv0 μ (AND f TRUE) f``,
rw[equiv0_def,satis_def,AND_def,TRUE_def] >> metis_tac[satis_in_world]);


val DNF_OF_def = Define`
DNF_OF f fs <=> DISJ_OF f {c | CONJ_OF c fs}`;

val DISJ_OF0_split = store_thm(
"DISJ_OF0_split",
``!f fs. DISJ_OF0 f fs ==> !t. t IN fs /\  ¬DISJ_OF0 f (fs DELETE t) ==>
?p. DISJ_OF p (fs DELETE t) /\ equiv0 μ f (DISJ t p)``,
Induct_on `DISJ_OF0` >> rw[]
>- (`f = t` by (SPOSE_NOT_THEN ASSUME_TAC >> `f IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases]) >>
   qexists_tac `FALSE` >>
   fs[DISJ_OF_def] >> rw[equiv0_def,satis_def,satis_in_world])
>- (Cases_on `t = f1`
   >- (rw[] >> qexists_tac `f` >> metis_tac[equiv0_REFL,DISJ_OF_def])
   >- (`¬DISJ_OF0 f (fs DELETE f1 DELETE t)` by (SPOSE_NOT_THEN ASSUME_TAC >>
            `(fs DELETE f1) DELETE t = (fs DELETE t) DELETE f1` by fs[DELETE_COMM] >>
            `DISJ_OF0 f (fs DELETE t DELETE f1)` by metis_tac[] >>
            `f1 IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases]) >>
      `∃p. DISJ_OF p (fs DELETE f1 DELETE t) ∧ equiv0 μ f (DISJ t p)` by metis_tac[] >>
      fs[DISJ_OF_def]
      >- (rw[] >>
         qexists_tac `f1` >> rw[]
         >- (`f1 IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases])
         >- (`equiv0 μ f t` by metis_tac[equiv0_DISJ_FALSE] >>
             fs[equiv0_def,satis_def] >> metis_tac[]))
      >- (qexists_tac `DISJ f1 p` >> rw[]
         >- (`f1 IN (fs DELETE t)` by fs[] >>
            `(fs DELETE f1 DELETE t) = (fs DELETE t DELETE f1)` by fs[DELETE_COMM] >>
            metis_tac[DISJ_OF0_cases])
         >- (`equiv0 μ (DISJ f1 f) (DISJ f1 (DISJ t p))` by metis_tac[equiv0_DISJ_subst] >>
            fs[equiv0_def,satis_def] >> metis_tac[])))));
             
val DNF_OF_DISJ_equiv0_case4 = store_thm(
"DNF_OF_DISJ_equiv0_case4",
``!p1 fs.  DISJ_OF0 p1 fs ==> (!p2. DISJ_OF0 p2 fs ==> ?f. DISJ_OF0 f fs /\ equiv0 μ f (DISJ p1 p2))``,
Induct_on `DISJ_OF0` >> rw[]
>- (`!p2 fs. DISJ_OF0 p2 fs ==> p1 IN fs ==> ∃f. DISJ_OF0 f fs ∧ equiv0 μ f (DISJ p1 p2)` suffices_by metis_tac[] >>
   rpt (pop_assum (K ALL_TAC)) >> Induct_on `DISJ_OF0` >> rw[]
   >- (Cases_on `p1 = p2`
      >- (qexists_tac `p1` >> rw[]
         >- metis_tac[DISJ_OF0_cases]
         >- metis_tac[equiv0_DISJ_absorb])
      >- (qexists_tac `DISJ p1 p2` >> rw[] >>
         `DISJ_OF0 p2 (fs DELETE p1)` by (`p2 IN (fs DELETE p1)` by fs[] >> metis_tac[DISJ_OF0_cases]) >>
         metis_tac[DISJ_OF0_cases]))
   >- (Cases_on `p1 = f1`
      >- (qexists_tac `DISJ f1 p2` >> rw[]
         >- metis_tac[DISJ_OF0_cases]
         >- metis_tac[equiv0_DISJ_DISJ_absorb])
      >- (`∃f. DISJ_OF0 f (fs DELETE f1) ∧ equiv0 μ f (DISJ p1 p2)` by metis_tac[] >>
         qexists_tac `DISJ f1 f` >> rw[]
         >- metis_tac[DISJ_OF0_cases]
         >- (`equiv0 μ (DISJ p1 (DISJ f1 p2)) (DISJ f1 (DISJ p1 p2))` by metis_tac[equiv0_DISJ_comm_assoc] >>
            `equiv0 μ (DISJ f1 (DISJ p1 p2)) (DISJ f1 f)` by metis_tac[equiv0_DISJ_subst,equiv0_SYM] >>
            metis_tac[equiv0_TRANS,equiv0_SYM]))))
>- (Cases_on `DISJ_OF0 p2 (fs DELETE f1)`
   >- (`∃f. DISJ_OF0 f (fs DELETE f1) ∧ equiv0 μ f (DISJ p1 p2)` by metis_tac[] >>
      qexists_tac `DISJ f1 f` >> rw[]
      >- metis_tac[DISJ_OF0_cases]
      >- (`equiv0 μ (DISJ (DISJ f1 p1) p2) (DISJ f1 (DISJ p1 p2))` by metis_tac[equiv0_DISJ_assoc] >>
         metis_tac[equiv0_DISJ_subst,equiv0_SYM,equiv0_TRANS]))
   >- (`?p. DISJ_OF p (fs DELETE f1) /\ equiv0 μ p2 (DISJ f1 p)` by metis_tac[DISJ_OF0_split] >> fs[DISJ_OF_def]
      >- (rw[] >>
         qexists_tac `DISJ f1 p1` >> rw[]
         >- metis_tac[DISJ_OF0_cases]
         >- (`equiv0 μ p2 f1` by metis_tac[equiv0_DISJ_FALSE] >>
            fs[equiv0_def,satis_def] >> metis_tac[]))
      >- (`?p. DISJ_OF0 p (fs DELETE f1) /\ equiv0 μ p2 (DISJ f1 p)` by metis_tac[DISJ_OF0_split] >>
         `∃f. DISJ_OF0 f (fs DELETE f1) ∧ equiv0 μ f (DISJ p1 p)` by metis_tac[] >>
         qexists_tac `DISJ f1 f` >> rw[]
         >- metis_tac[DISJ_OF0_cases]
         >- (`equiv0 μ (DISJ (DISJ f1 p1) p2) (DISJ (DISJ f1 p1) (DISJ f1 p))` by metis_tac[equiv0_DISJ_subst] >>
         `equiv0 μ (DISJ (DISJ f1 p1) (DISJ f1 p)) (DISJ f1 (DISJ p1 p))` by (rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]) >>
            `equiv0 μ (DISJ f1 (DISJ p1 p)) (DISJ f1 f)` by metis_tac[equiv0_SYM,equiv0_DISJ_subst] >>
            metis_tac[equiv0_SYM,equiv0_TRANS])))));
         
val DNF_OF_DISJ_equiv0 = store_thm(
"DNF_OF_DISJ_equiv0",
``!p1 p2 fs. DNF_OF p1 fs /\ DNF_OF p2 fs ==> ?f. DNF_OF f fs /\ equiv0 μ f (DISJ p1 p2)``,
rw[DNF_OF_def,DISJ_OF_def]
>- (qexists_tac `FALSE` >> metis_tac[equiv0_def,satis_def])
>- (qexists_tac `p2` >>
   `DISJ_OF0 p2 {c | CONJ_OF c fs} ∧ equiv0 μ p2 (DISJ ⊥ p2)` suffices_by metis_tac[] >> rw[] >>
   rw[equiv0_def,satis_def])
>- (qexists_tac `p1` >> rw[equiv0_def,satis_def])
>- (`?f. DISJ_OF0 f {c | CONJ_OF c fs} /\ equiv0 μ f (DISJ p1 p2)` by metis_tac[DNF_OF_DISJ_equiv0_case4] >>
   metis_tac[]));


val DNF_list_lemma = store_thm(
"DNF_list_lemma",
``!f fs. DNF_OF f fs ==>
?ld. f = lit_list_to_form2 ld /\ ALL_DISTINCT ld /\
(!d. d IN (set ld) ==>
(?lc. d = lit_list_to_form lc /\ set (MAP FST lc) = fs /\ ALL_DISTINCT (MAP FST lc)))``,
rw[DNF_OF_def,DISJ_OF_def]
>- (qexists_tac `[]` >> rw[])
>- (`∃l1. l1 ≠ [] ∧ set l1 ⊆ {c | CONJ_OF c fs} ∧ f = lit_list_to_form2 l1 ∧ ALL_DISTINCT l1` by metis_tac[DISJ_OF0_DISJ_lemma_EQ] >>
   qexists_tac `l1` >> rw[] >>
   `CONJ_OF d fs` by fs[SUBSET_DEF] >>
   `∃l2.
        set (MAP FST l2) = fs ∧ ALL_DISTINCT (MAP FST l2) ∧
        d = lit_list_to_form l2` by metis_tac[CONJ_OF_AND_lemma] >>
   qexists_tac `l2` >> rw[]));




val NOT_equiv0_OPPO = store_thm(
"NOT_equiv0_OPPO",
``!e. ¬(equiv0 μ (¬e) e)``,
SPOSE_NOT_THEN ASSUME_TAC >> fs[equiv0_def,satis_def] >> rw[] >>
`!M w. w ∈ M.frame.world ∧ ¬satis M w e ==> satis M w e` by metis_tac[] >>
`!M w. ¬(w ∈ M.frame.world ∧ ¬satis M w e) \/ satis M w e` by metis_tac[] >>
`!M w. ¬(w ∈ M.frame.world) \/ satis M w e` by metis_tac[] >>
`𝕌(:'b) <> {}` by metis_tac[UNIV_NOT_EMPTY] >>
`?m. m IN 𝕌(:'b)` by metis_tac[MEMBER_NOT_EMPTY] >>
`m IN <| frame := <| world := {m};
                           rel := λn1 n2. (n1 = m /\ n2 = m) |>;
                   valt := λe w. T|>.frame.world` by fs[] >>
`satis <|frame := <|world := {m}; rel := (λn1 n2. n1 = m ∧ n2 = m)|>;
        valt := (λe w. T)|> m e` by metis_tac[] >>
metis_tac[]);

val equiv0_AND_DISJ = store_thm(
"equiv0_AND_DISJ",
``!f g h. equiv0 μ (AND f (DISJ g h)) (DISJ (AND f g) (AND f h))``,
rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]);

val list_demorgan = store_thm(
"list_demorgan",
``!l. l <> [] ==> equiv0 μ (AND e (lit_list_to_form2 l)) (lit_list_to_form2 (MAP (λa. AND e a) l))``,
Induct_on `l` >> rw[] >> Cases_on `l = []` >> rw[] >>
`equiv0 μ (AND e (lit_list_to_form2 l)) (lit_list_to_form2 (MAP (λa. AND e a) l))` by metis_tac[] >>
Cases_on `l` >> rw[] >>
qmatch_abbrev_tac `equiv0 μ (AND e (DISJ h L)) (DISJ (AND e h) AL)` >>
`equiv0 μ (AND e (DISJ h L)) (DISJ (AND e h) (AND e L))` by metis_tac[equiv0_AND_DISJ] >>
metis_tac[equiv0_DISJ_subst,equiv0_SYM,equiv0_TRANS]);

val DISJ_list_CONS = store_thm(
"DISJ_list_CONS",
``!l. l = h :: t ==> equiv0 μ (DISJ h (lit_list_to_form2 t)) (lit_list_to_form2 l)``,
Cases_on `l` >> rw[] >> Cases_on `t` >> rw[] >> rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);

val DISJ_list_extract = store_thm(
"DISJ_list_extract",
``!l1 l2. l1 <> [] ==> equiv0 μ (DISJ (HD l1) (lit_list_to_form2 (TL (l1 ++ l2)))) (DISJ (lit_list_to_form2 l1) (lit_list_to_form2 l2))``,
Induct_on `l1` >> rw[] >> Cases_on `l1 = []` >> rw[] >>
`equiv0 μ (DISJ (HD l1) (lit_list_to_form2 (TL (l1 ⧺ l2))))
           (DISJ (lit_list_to_form2 l1) (lit_list_to_form2 l2))` by metis_tac[] >>
Cases_on `l1` >> rw[] >>
`equiv0 μ (lit_list_to_form2 (h'::(t ⧺ l2))) (DISJ h' (lit_list_to_form2 (t ++ l2)))` by metis_tac[DISJ_list_CONS,equiv0_SYM] >>
`equiv0 μ (DISJ (DISJ h (lit_list_to_form2 (h'::t))) (lit_list_to_form2 l2))
(DISJ h (DISJ (lit_list_to_form2 (h'::t)) (lit_list_to_form2 l2)))` by metis_tac[equiv0_DISJ_assoc] >>
`equiv0 μ (lit_list_to_form2 (h'::(t ⧺ l2))) (DISJ (lit_list_to_form2 (h'::t)) (lit_list_to_form2 l2))` suffices_by metis_tac[equiv0_DISJ_subst,equiv0_SYM,equiv0_TRANS] >>
metis_tac[equiv0_SYM,equiv0_TRANS]);


val FINITE_CONJ_OF_EXISTS_TRUE = store_thm(
"FINITE_CONJ_OF_EXISTS_TRUE",
``!fs. FINITE fs ==> fs <> {} ==> ?f. DNF_OF f fs /\ equiv0 μ f TRUE``,
Induct_on `FINITE fs` >> rw[] >>
Cases_on `fs = {}`
>- (`e INSERT fs = {e}` by fs[] >> rw[] >>
   qexists_tac `DISJ e (¬e)` >> rw[]
   >- (rw[DNF_OF_def,DISJ_OF_def] >> rw[Once DISJ_OF0_cases] >>
      `CONJ_OF e {e} ∧ DISJ_OF0 (¬e) ({c | CONJ_OF c {e}} DELETE e)` suffices_by metis_tac[] >> rw[]
      >- rw[Once CONJ_OF_cases]
      >- (`CONJ_OF (¬e) {e}` by fs[Once CONJ_OF_cases] >>
         `(¬e) IN ({c | CONJ_OF c {e}} DELETE e)` by (fs[] >> SPOSE_NOT_THEN ASSUME_TAC >>
         `equiv0 μ (¬e) e` by fs[] >> metis_tac[NOT_equiv0_OPPO]) >>
         metis_tac[DISJ_OF0_cases]))
   >- (rw[equiv0_def,satis_def,TRUE_def] >> metis_tac[satis_in_world]))
>- (`∃f. DNF_OF f fs ∧ equiv0 μ f TRUE` by metis_tac[] >>
   drule DNF_list_lemma >> rw[] >> 
   `(MAP (λa. AND e a) ld) <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> rw[] >> `ld = []` by fs[] >>
   rw[] >> fs[lit_list_to_form2_def] >> fs[TRUE_def] >> metis_tac[NOT_equiv0_OPPO,equiv0_SYM]) >>
   `equiv0 μ (DISJ (HD (MAP (λa. AND e a) ld)) (lit_list_to_form2 (TL ((MAP (λa. AND e a) ld) ++ (MAP (λa. AND (¬e) a) ld)))))
   (DISJ (lit_list_to_form2 (MAP (λa. AND e a) ld)) (lit_list_to_form2 (MAP (λa. AND (¬e) a) ld)))` by metis_tac[DISJ_list_extract] >>
   qexists_tac `DISJ (HD (MAP (λa. AND e a) ld))
           (lit_list_to_form2
              (TL (MAP (λa. AND e a) ld ⧺ MAP (λa. AND (¬e) a) ld)))` >> rw[]
   >- (rw[DNF_OF_def,DISJ_OF_def] >> rw[Once DISJ_OF0_cases] >>
      `CONJ_OF (HD (MAP (λa. AND e a) ld)) (e INSERT fs) ∧
DISJ_OF0
  (lit_list_to_form2
     (TL (MAP (λa. AND e a) ld ⧺ MAP (λa. AND (¬e) a) ld)))
  ({c | CONJ_OF c (e INSERT fs)} DELETE HD (MAP (λa. AND e a) ld))` suffices_by metis_tac[] >> rw[]
      >- (`HD (MAP (λa. AND e a) ld) = AND e (HD ld)` by (`ld <> []` by fs[] >> Cases_on `ld` >> rw[]) >>
         `ld <> []` by fs[] >> Cases_on `ld` >> rw[] >> fs[] >>
         `∃lc.
            h = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧
            ALL_DISTINCT (MAP FST lc)` by metis_tac[] >> rw[] >>
         `lc <> []` by fs[] >> 
         `AND e (lit_list_to_form lc) = lit_list_to_form ((e, T) :: lc)` by (Cases_on `lc` >> rw[]) >> rw[] >>
         irule list_to_CONJ_OF >> fs[])
      >- (`ld <> []` by fs[] >> Cases_on `ld` >> rw[] >> irule list_to_DISJ_OF0
         >- (fs[ALL_DISTINCT_APPEND] >> rw[]
            >- (irule ALL_DISTINCT_MAP_INJ >> rw[])
            >- (SPOSE_NOT_THEN ASSUME_TAC >> fs[MEM_MAP])
            >- (irule ALL_DISTINCT_MAP_INJ >> rw[])
            >- (fs[MEM_MAP] >> metis_tac[])
            >- (fs[MEM_MAP] >> SPOSE_NOT_THEN ASSUME_TAC >> `equiv0 μ e (¬e)` by metis_tac[equiv0_REFL] >> 
            metis_tac[NOT_equiv0_OPPO]))
         >- fs[]
         >- (rw[SUBSET_DEF]
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0 f1 f2.
                x = AND f1 f2 ∧ (f1 = f0 ∨ f1 = ¬f0) ∧ (f0 = e ∨ f0 ∈ fs) ∧
                CONJ_OF f2 ((e INSERT fs) DELETE f0)` suffices_by metis_tac[] >>
               fs[MEM_MAP] >>  qexists_tac `e` >> rw[] >>
               `((e INSERT fs) DELETE e) = fs` by (rw[Once DELETE_DEF,Once INSERT_DEF,EXTENSION] >> metis_tac[]) >>
               `∃lc.
                a = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧
                ALL_DISTINCT (MAP FST lc)` by metis_tac[] >>
               `lc <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> `set (MAP FST lc) = {}` by fs[] >> fs[]) >>
               metis_tac[list_to_CONJ_OF])
            >- (fs[MEM_MAP] >> metis_tac[])
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0.
               (¬e = f0 ∨ e = f0) ∧ (f0 = e ∨ f0 ∈ fs) ∧
               CONJ_OF h ((e INSERT fs) DELETE f0)` suffices_by metis_tac[] >>
               fs[MEM_MAP] >>  qexists_tac `e` >> rw[] >>
               `((e INSERT fs) DELETE e) = fs` by (rw[Once DELETE_DEF,Once INSERT_DEF,EXTENSION] >> metis_tac[]) >>
               `∃lc.
                h = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧
                ALL_DISTINCT (MAP FST lc)` by metis_tac[] >>
               `lc <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> `set (MAP FST lc) = {}` by fs[] >> fs[]) >>
               metis_tac[list_to_CONJ_OF])
            >- (`¬e <> e` suffices_by metis_tac[AND_INJ] >> SPOSE_NOT_THEN ASSUME_TAC >>
               `equiv0 μ (¬e) e` by metis_tac[equiv0_REFL] >> metis_tac[NOT_equiv0_OPPO])
            >- (fs[MEM_MAP] >>
               `∃lc.
               a = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧
               ALL_DISTINCT (MAP FST lc)` by metis_tac[] >>
               `lc <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> `set (MAP FST lc) = {}` by fs[] >> fs[]) >> 
               `AND (¬e) (lit_list_to_form lc) = lit_list_to_form ((e, F) :: lc)` by
               (Cases_on `lc` >> rw[]) >> rw[] >> irule list_to_CONJ_OF >> fs[])
            >- (fs[MEM_MAP] >> `¬e ≠ e` suffices_by metis_tac[] >> 
               SPOSE_NOT_THEN ASSUME_TAC >>
               `equiv0 μ (¬e) e` by metis_tac[equiv0_REFL] >> metis_tac[NOT_equiv0_OPPO]))))
   >- (`ld <> []` by fs[] >> Cases_on `ld` >> rw[] >>
      `(AND e h) = HD (MAP (λa. AND e a) (h::t))` by fs[] >>
      `MAP (λa. AND e a) t ⧺ AND (¬e) h::MAP (λa. AND (¬e) a) t =
      TL (MAP (λa. AND e a) (h::t) ⧺ MAP (λa. AND (¬e) a) (h::t))` by fs[] >> fs[] >>
      `equiv0 μ (DISJ (lit_list_to_form2 (AND e h::MAP (λa. AND e a) t))
      (lit_list_to_form2 (AND (¬e) h::MAP (λa. AND (¬e) a) t))) TRUE` suffices_by metis_tac[equiv0_TRANS] >>
      `(AND e h::MAP (λa. AND e a) t) = MAP (λa. AND e a) (h :: t)` by fs[] >>
      `(AND (¬e) h::MAP (λa. AND (¬e) a) t) = MAP (λa. AND (¬e) a) (h :: t)` by fs[] >> fs[] >>
      `h :: t <> []` by fs[] >>
      `equiv0 μ (lit_list_to_form2 (MAP (λa. AND e a) (h :: t)))
      (AND e (lit_list_to_form2 (h :: t)))` by metis_tac[list_demorgan,equiv0_SYM] >>
      `equiv0 μ (lit_list_to_form2 (MAP (λa. AND (¬e) a) (h :: t)))
      (AND (¬e) (lit_list_to_form2 (h :: t)))` by metis_tac[list_demorgan,equiv0_SYM] >>
      `equiv0 μ (AND e (lit_list_to_form2 (h::t))) (AND e TRUE)` by metis_tac[equiv0_AND_subst] >>
      `equiv0 μ (AND (¬e) (lit_list_to_form2 (h::t))) (AND (¬e) TRUE)` by metis_tac[equiv0_AND_subst] >>
      `equiv0 μ (AND e TRUE) e` by metis_tac[equiv0_TRUE_absorb] >>
      `equiv0 μ (AND (¬e) TRUE) (¬e)` by metis_tac[equiv0_TRUE_absorb] >> fs[] >>
      `equiv0 μ
      (DISJ (lit_list_to_form2 (AND e h::MAP (λa. AND e a) t))
      (lit_list_to_form2 (AND (¬e) h::MAP (λa. AND (¬e) a) t))) (DISJ e (¬e))` by (irule equiv0_DISJ_double_subst >>       metis_tac[equiv0_SYM,equiv0_TRANS]) >>
      `equiv0 μ (DISJ e (¬e)) TRUE` by metis_tac[equiv0_TAUT] >> metis_tac[equiv0_TRANS])));



val NOT_NEQ = store_thm(
"NOT_NEQ",
``!e. e <> ¬e /\ ¬e <> e``,
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >> `equiv0 μ (¬e) e` by metis_tac[equiv0_REFL,equiv0_SYM] >> metis_tac[NOT_equiv0_OPPO]);


val list_to_DNF_lemma = store_thm(
"list_to_DNF_lemma",
``!ld fs. ld <> [] /\ ALL_DISTINCT ld ∧
(∀d. MEM d ld ==>
(∃lc. lc <> [] /\ d = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧ ALL_DISTINCT (MAP FST lc))) ==>
DNF_OF (lit_list_to_form2 ld) fs``,
rw[DNF_OF_def,DISJ_OF_def] >>
`DISJ_OF0 (lit_list_to_form2 ld) {c | CONJ_OF c fs}` suffices_by metis_tac[] >>
irule list_to_DISJ_OF0 >> rw[] >>
rw[SUBSET_DEF] >> 
`∃lc. lc ≠ [] ∧ x = lit_list_to_form lc ∧ set (MAP FST lc) = fs ∧ ALL_DISTINCT (MAP FST lc)` by metis_tac[] >> rw[] >> irule list_to_CONJ_OF >> rw[]);


val lit_list_to_form2_CONS = store_thm(
"lit_list_to_form2_CONS",
``!h l. equiv0 μ (lit_list_to_form2 (h :: l)) (DISJ h (lit_list_to_form2 l))``,
Cases_on `l` >> rw[] >> metis_tac[equiv0_DISJ_F,equiv0_SYM]);



val equiv0_DISJ_IMP = store_thm(
"equiv0_DISJ_IMP",
``!f g. equiv0 μ (IMP f (DISJ f g)) TRUE``,
rw[TRUE_def,equiv0_def,satis_def,IMP_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_IMP_extend = store_thm(
"equiv0_DISJ_IMP_extend",
``!f g h. equiv0 μ (IMP f g) TRUE ==> equiv0 μ (IMP f (DISJ h g)) TRUE``,
rw[equiv0_def,IMP_def,TRUE_def,satis_def] >> metis_tac[satis_in_world]);

val equiv0_DISJ_IMP_AND = store_thm(
"equiv0_DISJ_IMP_AND",
``!f g h. equiv0 μ (IMP (DISJ f g) p) (AND (IMP f p) (IMP g p))``,
rw[equiv0_def,IMP_def,AND_def,satis_def] >> metis_tac[satis_in_world]);


val MEM_equiv0_TRUE2 = store_thm(
"MEM_equiv0_TRUE2",
``!l h. MEM h l ==> equiv0 μ (IMP (lit_list_to_form2 [h]) (lit_list_to_form2 l)) TRUE``,
Induct_on `l` >> simp[] >> rw[]
>- (`equiv0 μ (lit_list_to_form2 (h::l)) (DISJ h (lit_list_to_form2 l))` by metis_tac[lit_list_to_form2_CONS] >>
   `equiv0 μ (h -> lit_list_to_form2 (h::l))
    (h -> (DISJ h (lit_list_to_form2 l)))` by metis_tac[equiv0_IMP_subst] >>
   `equiv0 μ (h -> DISJ h (lit_list_to_form2 l)) TRUE` by metis_tac[equiv0_DISJ_IMP] >> metis_tac[equiv0_TRANS])
>- (`equiv0 μ (lit_list_to_form2 [h'] -> lit_list_to_form2 l) TRUE` by metis_tac[] >> fs[] >>
   `equiv0 μ (lit_list_to_form2 (h::l)) (DISJ h (lit_list_to_form2 l))` by metis_tac[lit_list_to_form2_CONS] >>
   `equiv0 μ (h' -> (DISJ h (lit_list_to_form2 l))) TRUE` suffices_by metis_tac[equiv0_SYM,equiv0_TRANS,equiv0_IMP_subst] >> metis_tac[equiv0_TRANS,equiv0_DISJ_IMP_extend]));



val lit_list_to_form_IMP_CONS2 = store_thm(
"lit_list_to_form_IMP_CONS2",
``equiv0 μ (IMP (lit_list_to_form2 (h :: l)) P) (AND (IMP (lit_list_to_form2 [h]) P) (IMP (lit_list_to_form2 l) P))``,
`equiv0 μ (lit_list_to_form2 (h :: l)) (DISJ h (lit_list_to_form2 l))` by metis_tac[lit_list_to_form2_CONS] >>
`equiv0 μ (lit_list_to_form2 (h::l) -> P) ((DISJ h (lit_list_to_form2 l)) -> P)` by metis_tac[equiv0_IMP_subst2,equiv0_SYM] >>
`equiv0 μ (DISJ h (lit_list_to_form2 l) -> P)
(AND (lit_list_to_form2 [h] -> P) (lit_list_to_form2 l -> P))` suffices_by metis_tac[equiv0_TRANS,equiv0_SYM] >>
fs[] >> metis_tac[equiv0_SYM,equiv0_TRANS,equiv0_DISJ_IMP_AND]);

val equiv0_CONJ_TRUE = store_thm(
"equiv0_CONJ_TRUE",
``!f g. equiv0 μ f TRUE /\ equiv0 μ g TRUE ==> equiv0 μ (AND f g) TRUE``,
rw[equiv0_def,satis_def,TRUE_def,AND_def] >> metis_tac[satis_in_world]);


val lit_list_to_form2_SUBSET = store_thm(
"lit_list_to_form_SUBSET",
``!l1 l2. (set l1) SUBSET (set l2) ==> equiv0 μ (IMP (lit_list_to_form2 l1) (lit_list_to_form2 l2)) TRUE``,
Induct_on `l1` >> simp[] >> rw[]
>- (rw[IMP_def,equiv0_def,TRUE_def,satis_def] >> metis_tac[satis_in_world])
>- (`equiv0 μ (lit_list_to_form2 l1 -> lit_list_to_form2 l2) TRUE` by metis_tac[] >>
   `equiv0 μ (lit_list_to_form2 [h] -> lit_list_to_form2 l2) TRUE` by metis_tac[MEM_equiv0_TRUE2] >>
   fs[] >>
   `equiv0 μ (lit_list_to_form2 (h::l1) -> lit_list_to_form2 l2)
   (AND (IMP (lit_list_to_form2 [h]) (lit_list_to_form2 l2)) (IMP (lit_list_to_form2 l1) (lit_list_to_form2 l2)))` by metis_tac[lit_list_to_form_IMP_CONS2] >> fs[] >> metis_tac[equiv0_TRANS,equiv0_SYM,equiv0_CONJ_TRUE]));
   




val lit_list_to_form2_SYM = store_thm(
"lit_list_to_form2_SYM",
``!l1 l2. set l1 = set l2 ==> equiv0 μ (lit_list_to_form2 l1) (lit_list_to_form2 l2)``,
rw[] >>
`(set l1) SUBSET (set l2) /\ (set l2) SUBSET (set l1)` by metis_tac[SET_EQ_SUBSET] >>
`equiv0 μ (IMP (lit_list_to_form2 l2) (lit_list_to_form2 l1)) TRUE /\
 equiv0 μ (IMP (lit_list_to_form2 l1) (lit_list_to_form2 l2)) TRUE` by metis_tac[lit_list_to_form2_SUBSET] >> metis_tac[equiv0_double_IMP]);




val CONJ_list_HD = store_thm(
"CONJ_list_HD",
``!l a. MEM a l /\ ALL_DISTINCT l ==> ?l'. equiv0 μ (lit_list_to_form l) (lit_list_to_form l') /\ set l = set l' /\ ALL_DISTINCT l' /\ HD l' = a``,
Induct_on `l` >> rw[]
>- (qexists_tac `a :: l` >> rw[])
>- (`∃l'. equiv0 μ (lit_list_to_form l) (lit_list_to_form l') ∧ set l = set l' ∧ ALL_DISTINCT l' ∧ HD l' = a` by metis_tac[] >>
   qexists_tac `SNOC h l'` >> rw[]
   >- (irule lit_list_to_form_SYM >> fs[LIST_TO_SET_SNOC])
   >- fs[LIST_TO_SET_SNOC]
   >- fs[ALL_DISTINCT_SNOC]
   >- (fs[SNOC_APPEND] >> `l' <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
      Cases_on `l'` >> rw[])));

val DISJ_list_HD = store_thm(
"DISJ_list_HD",
``!l a. MEM a l /\ ALL_DISTINCT l ==> ?l'. equiv0 μ (lit_list_to_form2 l) (lit_list_to_form2 l') /\ set l = set l' /\ ALL_DISTINCT l' /\ HD l' = a``,
Induct_on `l` >> rw[]
>- (qexists_tac `a :: l` >> rw[])
>- (`∃l'. equiv0 μ (lit_list_to_form2 l) (lit_list_to_form2 l') ∧ set l = set l' ∧ ALL_DISTINCT l' ∧ HD l' = a` by metis_tac[] >>
   qexists_tac `SNOC h l'` >> rw[]
   >- (irule lit_list_to_form2_SYM >> fs[LIST_TO_SET_SNOC])
   >- fs[LIST_TO_SET_SNOC]
   >- fs[ALL_DISTINCT_SNOC]
   >- (fs[SNOC_APPEND] >> `l' <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
      Cases_on `l'` >> rw[])));


val DISJ_OF0_split = store_thm(
"DISJ_OF0_split",
``!f fs. DISJ_OF0 f fs ==> !t. t IN fs /\  ¬DISJ_OF0 f (fs DELETE t) ==>
?p. DISJ_OF p (fs DELETE t) /\ equiv0 μ f (DISJ t p)``,
Induct_on `DISJ_OF0` >> rw[]
>- (`f = t` by (SPOSE_NOT_THEN ASSUME_TAC >> `f IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases]) >>
   qexists_tac `FALSE` >>
   fs[DISJ_OF_def] >> rw[equiv0_def,satis_def,satis_in_world])
>- (Cases_on `t = f1`
   >- (rw[] >> qexists_tac `f` >> metis_tac[equiv0_REFL,DISJ_OF_def])
   >- (`¬DISJ_OF0 f (fs DELETE f1 DELETE t)` by (SPOSE_NOT_THEN ASSUME_TAC >>
            `(fs DELETE f1) DELETE t = (fs DELETE t) DELETE f1` by fs[DELETE_COMM] >>
            `DISJ_OF0 f (fs DELETE t DELETE f1)` by metis_tac[] >>
            `f1 IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases]) >>
      `∃p. DISJ_OF p (fs DELETE f1 DELETE t) ∧ equiv0 μ f (DISJ t p)` by metis_tac[] >>
      fs[DISJ_OF_def]
      >- (rw[] >>
         qexists_tac `f1` >> rw[]
         >- (`f1 IN (fs DELETE t)` by fs[] >> metis_tac[DISJ_OF0_cases])
         >- (`equiv0 μ f t` by metis_tac[equiv0_DISJ_FALSE] >>
             fs[equiv0_def,satis_def] >> metis_tac[]))
      >- (qexists_tac `DISJ f1 p` >> rw[]
         >- (`f1 IN (fs DELETE t)` by fs[] >>
            `(fs DELETE f1 DELETE t) = (fs DELETE t DELETE f1)` by fs[DELETE_COMM] >>
            metis_tac[DISJ_OF0_cases])
         >- (`equiv0 μ (DISJ f1 f) (DISJ f1 (DISJ t p))` by metis_tac[equiv0_DISJ_subst] >>
            fs[equiv0_def,satis_def] >> metis_tac[])))));

val CONJ_OF_split = store_thm(
"CONJ_OF_split",
``!f fs. CONJ_OF f fs ==> !t. t IN fs /\ fs DELETE t <> {} ==>
?p. CONJ_OF p (fs DELETE t) /\ (equiv0 μ f (AND t p) \/ equiv0 μ f (AND (¬t) p))``,
Induct_on `CONJ_OF` >> rw[] (** 2 **)
>- (Cases_on `t <> f0` >> rw[] (** 2 **)
   >- (Cases_on `fs DELETE f0 DELETE t = ∅` >> rw[] (** 2 **)
      >- (`fs = {f0 ; t}` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
         `fs DELETE f0 = {t}` by (fs[DELETE_DEF,EXTENSION] >> metis_tac[]) >>
         `fs DELETE t = {f0}` by (fs[DELETE_DEF,EXTENSION] >> metis_tac[]) >> fs[] >>
         `f = t \/ f = ¬t` by (fs[Once CONJ_OF_cases] >> metis_tac[CONJ_OF_FINITE]) >> (** 2 (same) **)
         (qexists_tac `f0` >> rw[] >- metis_tac[CONJ_OF_cases]
                                   >- metis_tac[equiv0_AND_SYM]))
      >- (`∃p.
            CONJ_OF p (fs DELETE f0 DELETE t) ∧
            (equiv0 μ f (AND t p) ∨ equiv0 μ f (AND (¬t) p))` by metis_tac[] (** 2 **)
         >- (qexists_tac `AND f0 p` >> rw[] (** 2 **)
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0'.
               (f0 = f0' ∨ f0 = ¬f0') ∧ f0' ∈ fs ∧ f0' ≠ t ∧
               CONJ_OF p (fs DELETE t DELETE f0')` suffices_by metis_tac[] >>
               `fs DELETE t DELETE f0 = (fs DELETE f0 DELETE t)` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
               metis_tac[])
            >- (`equiv0 μ (AND f0 f) (AND f0 (AND t p))` by metis_tac[equiv0_AND_subst] >>
               `equiv0 μ (AND f0 (AND t p)) (AND t (AND f0 p))` by (rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]) >>
               metis_tac[equiv0_SYM,equiv0_TRANS]))
         >- (qexists_tac `AND f0 p` >> rw[] (** 2 **)
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0'.
               (f0 = f0' ∨ f0 = ¬f0') ∧ f0' ∈ fs ∧ f0' ≠ t ∧
               CONJ_OF p (fs DELETE t DELETE f0')` suffices_by metis_tac[] >>
               `fs DELETE t DELETE f0 = (fs DELETE f0 DELETE t)` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
               metis_tac[])
            >- (`equiv0 μ (AND f0 f) (AND f0 (AND (¬t) p))` by metis_tac[equiv0_AND_subst] >>
               `equiv0 μ (AND f0 (AND (¬t) p)) (AND (¬t) (AND f0 p))` by (rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]) >>
               metis_tac[equiv0_SYM,equiv0_TRANS]))))
   >- (qexists_tac `f` >> rw[]))
>- (Cases_on `t <> f0` >> rw[] (** 2 **)
   >- (Cases_on `fs DELETE f0 DELETE t = {}` >> rw[] (** 2 **)
      >- (`fs = {f0 ; t}` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
         `fs DELETE f0 = {t}` by (fs[DELETE_DEF,EXTENSION] >> metis_tac[]) >>
         `fs DELETE t = {f0}` by (fs[DELETE_DEF,EXTENSION] >> metis_tac[]) >> fs[] >>
         `f = t \/ f = ¬t` by (fs[Once CONJ_OF_cases] >> metis_tac[CONJ_OF_FINITE]) >> (** 2 (same) **)
         (qexists_tac `¬f0` >> rw[] >- metis_tac[CONJ_OF_cases]
                                    >- metis_tac[equiv0_AND_SYM]))
      >- (`∃p.
            CONJ_OF p (fs DELETE f0 DELETE t) ∧
            (equiv0 μ f (AND t p) ∨ equiv0 μ f (AND (¬t) p))` by metis_tac[] (** 2 **)
         >- (qexists_tac `AND (¬f0) p` >> rw[] (** 2 **)
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0'.
               (¬f0 = f0' ∨ f0 = f0') ∧ f0' ∈ fs ∧ f0' ≠ t ∧
               CONJ_OF p (fs DELETE t DELETE f0')` suffices_by metis_tac[] >>
               `fs DELETE t DELETE f0 = (fs DELETE f0 DELETE t)` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
               metis_tac[])
            >- (`equiv0 μ (AND (¬f0) f) (AND (¬f0) (AND t p))` by metis_tac[equiv0_AND_subst] >>
               `equiv0 μ (AND (¬f0) (AND t p)) (AND t (AND (¬f0) p))` by (rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]) >>
               metis_tac[equiv0_SYM,equiv0_TRANS]))
         >- (qexists_tac `AND (¬f0) p` >> rw[] (** 2 **)
            >- (rw[Once CONJ_OF_cases] >>
               `∃f0'.
               (¬f0 = f0' ∨ f0 = f0') ∧ f0' ∈ fs ∧ f0' ≠ t ∧
               CONJ_OF p (fs DELETE t DELETE f0')` suffices_by metis_tac[] >>
               `fs DELETE t DELETE f0 = (fs DELETE f0 DELETE t)` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
               metis_tac[])
            >- (`equiv0 μ (AND (¬f0) f) (AND (¬f0) (AND (¬t) p))` by metis_tac[equiv0_AND_subst] >>
               `equiv0 μ (AND (¬t) (AND (¬f0) p)) (AND (¬f0) (AND (¬t) p))` by (rw[equiv0_def,satis_def,AND_def] >> metis_tac[satis_in_world]) >>
               metis_tac[equiv0_SYM,equiv0_TRANS]))))
   >- (qexists_tac `f` >> rw[])));
   
               
val equiv0_contra_IMP_everything = store_thm(
"equiv0_contra_IMP_everything",
``!f. equiv0 μ (IMP FALSE f) TRUE``,
rw[equiv0_def,satis_def,IMP_def,TRUE_def] >> metis_tac[satis_in_world]);

val DISJ_list_HD_MEM = store_thm(
"DISJ_list_HD_MEM",
``!l a. MEM a l ==> ?l'. equiv0 μ (lit_list_to_form2 l) (lit_list_to_form2 l') /\ set l = set l' /\ HD l' = a``,
Induct_on `l` >> rw[]
>- (qexists_tac `a :: l` >> rw[])
>- (`∃l'. equiv0 μ (lit_list_to_form2 l) (lit_list_to_form2 l') ∧ set l = set l' ∧ HD l' = a` by metis_tac[] >>
   qexists_tac `SNOC h l'` >> rw[]
   >- (irule lit_list_to_form2_SYM >> fs[LIST_TO_SET_SNOC])
   >- fs[LIST_TO_SET_SNOC]
   >- (fs[SNOC_APPEND] >> `l' <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
      Cases_on `l'` >> rw[])));

val MEM_equiv0_DISJ_IMP = store_thm(
"MEM_equiv0_DISJ_IMP",
``!l b h. MEM b l /\ equiv0 μ h b ==> equiv0 μ (h -> lit_list_to_form2 l) TRUE``,
rw[] >> drule DISJ_list_HD_MEM >> rw[] >>
`equiv0 μ (h -> lit_list_to_form2 l') TRUE` suffices_by metis_tac[equiv0_IMP_subst,equiv0_SYM,equiv0_TRANS] >>
Cases_on `l'` >> rw[] (** 2 **)
>- (`l <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[MEM]) >>
   `set [] = {}` by fs[] >> fs[])
>- (fs[] >>
   `equiv0 μ (lit_list_to_form2 (h'::t)) (DISJ h' (lit_list_to_form2 t))` by metis_tac[lit_list_to_form2_CONS] >>
   `equiv0 μ (h' -> lit_list_to_form2 (h'::t)) TRUE` suffices_by metis_tac[equiv0_IMP_subst2,equiv0_SYM,equiv0_TRANS] >>
   `equiv0 μ (h' -> (DISJ h' (lit_list_to_form2 t))) TRUE` suffices_by metis_tac[equiv0_IMP_subst,equiv0_SYM,equiv0_TRANS] >> metis_tac[equiv0_DISJ_IMP]));
   


val list_DISJ_equiv0_IMP_lemma = store_thm(
"list_DISJ_equiv0_IMP_lemma",
``!l1 l2. (!a. MEM a l1 ==> ?b. MEM b l2 /\ equiv0 μ a b) ==>
equiv0 μ (IMP (lit_list_to_form2 l1) (lit_list_to_form2 l2)) TRUE``,
Induct_on `l1` >> rw[]
>- metis_tac[equiv0_contra_IMP_everything]
>- (`(∀a. MEM a l1 ⇒ ∃b. MEM b l2 ∧ equiv0 μ a b)` by metis_tac[] >>
   `equiv0 μ (lit_list_to_form2 l1 -> lit_list_to_form2 l2) TRUE` by metis_tac[] >>
   `equiv0 μ (lit_list_to_form2 (h::l1)) (DISJ h (lit_list_to_form2 l1))` by metis_tac[lit_list_to_form2_CONS] >>
   `equiv0 μ (lit_list_to_form2 (h::l1) -> lit_list_to_form2 l2)
   ((DISJ h (lit_list_to_form2 l1)) -> lit_list_to_form2 l2)` by metis_tac[equiv0_IMP_subst2] >>
   `equiv0 μ (DISJ h (lit_list_to_form2 l1) -> lit_list_to_form2 l2) TRUE` suffices_by metis_tac[equiv0_SYM,equiv0_TRANS] >>
   `equiv0 μ (IMP h (lit_list_to_form2 l2)) TRUE` suffices_by metis_tac[equiv0_IMP_DISJ_TRUE] >>
   `∃b. MEM b l2 ∧ equiv0 μ h b` by metis_tac[] >>
   metis_tac[MEM_equiv0_DISJ_IMP]));


val list_DISJ_equiv0_SUBSET_lemma = store_thm(
"list_DISJ_equiv0_SUBSET_lemma",
``!l1 l2. (set l2) SUBSET (set l1) /\ (!a. MEM a l1 ==> ?b. MEM b l2 /\ equiv0 μ a b) ==>
equiv0 μ (lit_list_to_form2 l1) (lit_list_to_form2 l2)``,
rw[] >>
`equiv0 μ (IMP (lit_list_to_form2 l1) (lit_list_to_form2 l2)) TRUE /\
equiv0 μ (IMP (lit_list_to_form2 l2) (lit_list_to_form2 l1)) TRUE` suffices_by metis_tac[equiv0_double_IMP] >> rw[]
>- (irule list_DISJ_equiv0_IMP_lemma >> rw[])
>- (irule list_DISJ_equiv0_IMP_lemma >> rw[] >> qexists_tac `a` >> rw[] >> fs[SUBSET_DEF]));


val lit_list_to_form2_APPEND = store_thm(
"lit_list_to_form2_APPEND",
``!l1 l2. equiv0 μ (DISJ (lit_list_to_form2 l1) (lit_list_to_form2 l2)) (lit_list_to_form2 (l1 ++ l2))``,
Induct_on `l1` >> simp[]
>- metis_tac[equiv0_DISJ_F]
>- (Cases_on `l1` >> simp[]
   >- (Cases_on `l2` >> simp[] >> metis_tac[equiv0_DISJ_F])
   >- (rw[] >>
      `equiv0 μ (DISJ (DISJ h' (lit_list_to_form2 (h::t))) (lit_list_to_form2 l2)) (DISJ h' (DISJ (lit_list_to_form2 (h::t)) (lit_list_to_form2 l2)))` by metis_tac[equiv0_DISJ_assoc] >>
      `equiv0 μ (DISJ h' (DISJ (lit_list_to_form2 (h::t)) (lit_list_to_form2 l2))) (DISJ h' (lit_list_to_form2 (h::(t ⧺ l2))))` suffices_by metis_tac[equiv0_TRANS,equiv0_SYM] >>
      `equiv0 μ (DISJ (lit_list_to_form2 (h::t)) (lit_list_to_form2 l2)) (lit_list_to_form2 (h::t ⧺ l2))` by metis_tac[] >>
      irule equiv0_DISJ_subst >>
      `h :: (t ++ l2) = h :: t ++ l2` by simp[] >> metis_tac[])));


val CONJ_OF_NONEMPTY = store_thm(
"CONJ_OF_NONEMPTY",
``!s. FINITE s ==> s <> {} ==> {c | CONJ_OF c s} <> {}``,
Induct_on `FINITE s` >> rw[] >> Cases_on `s = {}` >> rw[]
>- (`e IN {c | CONJ_OF c {e}}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >> metis_tac[CONJ_OF_cases])
>- (`{c | CONJ_OF c s} ≠ ∅` by metis_tac[] >>
   `?a. a IN {c | CONJ_OF c s}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >>
   `?b. b IN {c | CONJ_OF c (e INSERT s)}`suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
   qexists_tac `AND e a` >> rw[] >> rw[Once CONJ_OF_cases] >>
   `∃f0.
   (e = f0 ∨ e = ¬f0) ∧ (f0 = e ∨ f0 ∈ s) ∧
   CONJ_OF a ((e INSERT s) DELETE f0)` suffices_by metis_tac[] >> qexists_tac `e` >> rw[] >>
   `((e INSERT s) DELETE e) = s` by (rw[EXTENSION] >> metis_tac[]) >>
   metis_tac[]));
   



val CONJ_OF_CONS_FINITE = store_thm(
"CONJ_OF_CONS_FINITE",
``!s. FINITE s /\ s <> {} ==> FINITE {AND f c | c | CONJ_OF c s} /\
{AND f c | c | CONJ_OF c s} <> {}``,
rw[]
>- (`{AND f c | CONJ_OF c s} = IMAGE (λc. (AND f c)) {c | CONJ_OF c s}` by simp[EXTENSION] >>
   `FINITE {c | CONJ_OF c s}` suffices_by fs[] >>
   metis_tac[FINITE_CONJ_OF])
>- (`{AND f c | CONJ_OF c s} = IMAGE (λc. (AND f c)) {c | CONJ_OF c s}` by simp[EXTENSION] >>
   `{c | CONJ_OF c s} <> {}` suffices_by fs[] >>
   metis_tac[CONJ_OF_NONEMPTY]));
 

val EACH_MEM_IMP_list = store_thm(
"EACH_MEM_IMP_list",
``!l. (!a. MEM a l ==> equiv0 μ (IMP a f) TRUE) ==> equiv0 μ (IMP (lit_list_to_form2 l) f) TRUE``,
Induct_on `l` >> rw[]
>- (rw[equiv0_def,IMP_def,TRUE_def,satis_def] >> metis_tac[satis_in_world])
>- (Cases_on `l` >> rw[] >>
   `!a. MEM a (h'::t) ⇒ equiv0 μ (a -> f) TRUE` by metis_tac[] >>
   `equiv0 μ (lit_list_to_form2 (h'::t) -> f) TRUE` by metis_tac[] >>
   `equiv0 μ (h -> f) TRUE` by metis_tac[] >> metis_tac[equiv0_IMP_DISJ_TRUE]));
   
 




val ALL_POSSIBLE_VALUE_TRUE = store_thm(
"ALL_POSSIBLE_VALUE_TRUE",
``!fs. FINITE fs ==> fs <> {} ==> equiv0 μ (lit_list_to_form2 (SET_TO_LIST {c| CONJ_OF c fs})) TRUE``,
Induct_on `FINITE` >> rw[] >>
Cases_on `fs = {}` >> rw[]
>- (`{c | CONJ_OF c {e}} = {e; (¬e)}` by (simp[EXTENSION] >> rw[Once CONJ_OF_cases] >> metis_tac[CONJ_OF_FINITE]) >>
   fs[] >>
   `FINITE {e; ¬e}` by fs[] >>
   `set (SET_TO_LIST {e; ¬e}) = {e; ¬e}` by fs[SET_TO_LIST_INV] >>
   `set [e; ¬e] = {e; ¬e}` by fs[] >>
   `lit_list_to_form2 [e; (¬e)] = DISJ e (¬e)` by rw[lit_list_to_form2_def] >>
   `equiv0 μ (DISJ e (¬e)) TRUE` by metis_tac[equiv0_TAUT] >>
   `equiv0 μ (lit_list_to_form2 (SET_TO_LIST {e; ¬e})) (lit_list_to_form2 [e; ¬e])` by metis_tac[lit_list_to_form2_SYM] >>
   metis_tac[equiv0_SYM,equiv0_TRANS])
>- (`equiv0 μ (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c fs})) TRUE` by metis_tac[] >>
   `FINITE {c | CONJ_OF c fs}` by metis_tac[FINITE_CONJ_OF] >>
   `FINITE (e INSERT fs)` by fs[] >>
   `FINITE {c | CONJ_OF c (e INSERT fs)}` by metis_tac[FINITE_CONJ_OF] >>
   (** setup subgoal to prove equal of the equiv0alence classes of set members **)
   `equiv0 μ (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c (e INSERT fs)}))
   (lit_list_to_form2 (SET_TO_LIST ({AND e a | a | CONJ_OF a fs} UNION {AND (¬e) a | a | CONJ_OF a fs})))` by
      (irule list_DISJ_equiv0_SUBSET_lemma >> rw[] (** 2 **)
      >- (`FINITE {AND e c | CONJ_OF c fs} ∧ {AND e c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
        `FINITE {AND (¬e) c | CONJ_OF c fs} ∧ {AND (¬e) c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
        `e IN (e INSERT fs)` by fs[] >>
        `(e INSERT fs) DELETE e = fs` by (fs[INSERT_DEF,DELETE_DEF,EXTENSION] >> metis_tac[]) >>
        `∃p.
           CONJ_OF p ((e INSERT fs) DELETE e) ∧
           (equiv0 μ a (AND e p) ∨ equiv0 μ a (AND (¬e) p))` by metis_tac[CONJ_OF_split] (** 2 **)
             >- (qexists_tac `AND e p` >> rw[] >> fs[] >> metis_tac[])
             >- (qexists_tac `AND (¬e) p` >> rw[] >> fs[] >> metis_tac[]))
       >- (`FINITE {AND e c | CONJ_OF c fs} ∧ {AND e c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
         `FINITE {AND (¬e) c | CONJ_OF c fs} ∧ {AND (¬e) c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
         `FINITE ({AND e a | CONJ_OF a fs} ∪ {AND (¬e) a | CONJ_OF a fs})` by fs[] >>
         fs[SET_TO_LIST_INV] >> rw[] >> fs[SUBSET_DEF] >> rw[] (** 2 same **)
         >> (`(e INSERT fs) DELETE e = fs` by (fs[INSERT_DEF,EXTENSION,DELETE_DEF] >> metis_tac[]) >>
         `e IN (e INSERT fs)` by fs[] >>
         metis_tac[CONJ_OF_cases]))) >>
   (** the subgoal setup above proved **)
   `equiv0 μ (lit_list_to_form2
           (SET_TO_LIST
              ({AND e a | CONJ_OF a fs} ∪ {AND (¬e) a | CONJ_OF a fs})))
          (lit_list_to_form2
           ((SET_TO_LIST {AND e a | CONJ_OF a fs}) ++ (SET_TO_LIST {AND (¬e) a | CONJ_OF a fs})))` by
      (** setup subgoal to split the big set to list to two lists **)
      (irule lit_list_to_form2_SYM >> rw[] >>
      `FINITE {AND e c | CONJ_OF c fs} ∧ {AND e c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
      `FINITE {AND (¬e) c | CONJ_OF c fs} ∧ {AND (¬e) c | CONJ_OF c fs} ≠ ∅` by metis_tac[CONJ_OF_CONS_FINITE] >>
      `FINITE ({AND e a | CONJ_OF a fs} ∪ {AND (¬e) a | CONJ_OF a fs})` by fs[] >>
      fs[SET_TO_LIST_INV]) >>
      (** subgoal setup above proved **)
   (** split the list into DISJ **) 
   `equiv0 μ (lit_list_to_form2
                (SET_TO_LIST {AND e a | CONJ_OF a fs} ⧺
                 SET_TO_LIST {AND (¬e) a | CONJ_OF a fs}))
          (DISJ (lit_list_to_form2 (SET_TO_LIST {AND e a | CONJ_OF a fs}))
                 (lit_list_to_form2 (SET_TO_LIST {AND (¬e) a | CONJ_OF a fs})))` by metis_tac[lit_list_to_form2_APPEND,equiv0_SYM] >>
   (** list splited **)
   (** discuss the two lists respectively **)
   (** the first list **)
   `equiv0 μ (lit_list_to_form2 (SET_TO_LIST {AND e a | CONJ_OF a fs}))
   (AND e TRUE)` by
       (** compare list with same member **)
       (`equiv0 μ (lit_list_to_form2 (SET_TO_LIST {AND e a | CONJ_OF a fs}))
       (lit_list_to_form2 (MAP (λa. AND e a) (SET_TO_LIST {c | CONJ_OF c fs})))` by
       (irule lit_list_to_form2_SYM >> rw[] >>
       `FINITE {AND e a | CONJ_OF a fs}` by metis_tac[CONJ_OF_CONS_FINITE] >>
       `FINITE {c | CONJ_OF c fs}` by metis_tac[FINITE_CONJ_OF] >> fs[MEM_MAP,SET_TO_LIST_INV,EXTENSION]) >>
       (** equiv0alence by same member proved **)
       (** use distributive law to extract the e **)
       `{c | CONJ_OF c fs} <> {}` by metis_tac[CONJ_OF_NONEMPTY] >>
       `set (SET_TO_LIST {c | CONJ_OF c fs}) = {c | CONJ_OF c fs}` by metis_tac[SET_TO_LIST_INV] >>
       `SET_TO_LIST {c | CONJ_OF c fs} <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
       `equiv0 μ (AND e (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c fs})))
       (lit_list_to_form2
            (MAP (λa. AND e a) (SET_TO_LIST {c | CONJ_OF c fs})))` by metis_tac[list_demorgan] >>
       `equiv0 μ (AND e (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c fs})))
       (AND e TRUE)` by metis_tac[equiv0_AND_subst] >> metis_tac[equiv0_SYM,equiv0_TRANS]) >>
   (** end of first list **)
   (** second list **)
   `equiv0 μ (lit_list_to_form2 (SET_TO_LIST {AND (¬e) a | CONJ_OF a fs}))
   (AND (¬e) TRUE)` by 
       (** compare list with same member **)
       (`equiv0 μ (lit_list_to_form2 (SET_TO_LIST {AND (¬e) a | CONJ_OF a fs}))
       (lit_list_to_form2 (MAP (λa. AND (¬e) a) (SET_TO_LIST {c | CONJ_OF c fs})))` by
       (irule lit_list_to_form2_SYM >> rw[] >>
       `FINITE {AND (¬e) a | CONJ_OF a fs}` by metis_tac[CONJ_OF_CONS_FINITE] >>
       `FINITE {c | CONJ_OF c fs}` by metis_tac[FINITE_CONJ_OF] >> fs[MEM_MAP,SET_TO_LIST_INV,EXTENSION]) >>
       (** equiv0alence by same member proved **)
       (** use distributive law to extract the e **)
       `{c | CONJ_OF c fs} <> {}` by metis_tac[CONJ_OF_NONEMPTY] >>
       `set (SET_TO_LIST {c | CONJ_OF c fs}) = {c | CONJ_OF c fs}` by metis_tac[SET_TO_LIST_INV] >>
       `SET_TO_LIST {c | CONJ_OF c fs} <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
       `equiv0 μ (AND (¬e) (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c fs})))
       (lit_list_to_form2
            (MAP (λa. AND (¬e) a) (SET_TO_LIST {c | CONJ_OF c fs})))` by metis_tac[list_demorgan] >>
       `equiv0 μ (AND (¬e) (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c fs})))
       (AND (¬e) TRUE)` by metis_tac[equiv0_AND_subst] >> metis_tac[equiv0_SYM,equiv0_TRANS]) >>
   (** end of second list **)
   `equiv0 μ (DISJ
            (lit_list_to_form2 (SET_TO_LIST {AND e a | CONJ_OF a fs}))
            (lit_list_to_form2
               (SET_TO_LIST {AND (¬e) a | CONJ_OF a fs})))
          (DISJ (AND e TRUE) (AND (¬e) TRUE))` by metis_tac[equiv0_SYM,equiv0_TRANS,equiv0_DISJ_double_subst] >>
   `equiv0 μ (DISJ (AND e TRUE) (AND (¬e) TRUE)) TRUE` by (rw[equiv0_def,AND_def,TRUE_def,satis_def] >> metis_tac[satis_in_world]) >> metis_tac[equiv0_SYM,equiv0_TRANS]));





val IBC_DNF_EXISTS_case4 = store_thm(
"IBC_DNF_EXISTS_case4",
``!fs. FINITE fs /\ fs <> {} ==> !f. f IN fs ==> ?p. DNF_OF p fs /\ equiv0 μ f p``,
rw[] >> Cases_on `fs = {f}`
>- (qexists_tac `f` >> rw[DNF_OF_def,DISJ_OF_def,Once DISJ_OF0_cases] >> metis_tac[CONJ_OF_cases])
>> (`fs DELETE f <> {}` by (fs[EXTENSION,DELETE_DEF] >> metis_tac[]) >>
   `FINITE (fs DELETE f)` by fs[] >>
   `FINITE {AND f c | c | CONJ_OF c (fs DELETE f)}` by metis_tac[CONJ_OF_CONS_FINITE] >>
   `{AND f c | c | CONJ_OF c (fs DELETE f)} ≠ {}` by metis_tac[CONJ_OF_CONS_FINITE] >>
   qexists_tac `lit_list_to_form2 (SET_TO_LIST {AND f c | c | CONJ_OF c (fs DELETE f)})` >> rw[]
    >- (irule list_to_DNF_lemma 
       >- (rw[] >>
          drule CONJ_OF_AND_lemma >> rw[] >>
          qexists_tac `(f, T) :: l` >> rw[] >>
          `l <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> `fs DELETE f = {}` by fs[] >> metis_tac[CONJ_OF_FINITE]) >>
          Cases_on `l` >> rw[])
       >-  metis_tac[ALL_DISTINCT_SET_TO_LIST]
       >- (`?a. a IN {AND f c | c | CONJ_OF c (fs DELETE f)}` by fs[MEMBER_NOT_EMPTY] >>
          `MEM a (SET_TO_LIST {AND f c | c | CONJ_OF c (fs DELETE f)})` by fs[Once SET_TO_LIST_IN_MEM] >>
          SPOSE_NOT_THEN ASSUME_TAC >> fs[])))
    >- (`FINITE (fs DELETE f)` by fs[] >>
       `FINITE {c | CONJ_OF c (fs DELETE f)}` by metis_tac[FINITE_CONJ_OF] >>
       `(SET_TO_LIST {c | CONJ_OF c (fs DELETE f)}) <> []` by
        (SPOSE_NOT_THEN ASSUME_TAC >>
       `set (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)}) = {c | CONJ_OF c (fs DELETE f)}` by metis_tac[SET_TO_LIST_INV] >>
       `{c | CONJ_OF c (fs DELETE f)} <> {}` by metis_tac[CONJ_OF_NONEMPTY] >>
       `set (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)}) = {}` by fs[] >> fs[]) >>
       `equiv0 μ (AND f (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)})))
       (lit_list_to_form2 (MAP (λa. AND f a) (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)})))` by metis_tac[list_demorgan] >>
       `set (MAP (λa. AND f a) (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)})) = {AND f c | c | CONJ_OF c (fs DELETE f)}` by (simp[EXTENSION] >> rw[] >> fs[MEM_MAP]) >>
       `set (SET_TO_LIST {AND f c | c | CONJ_OF c (fs DELETE f)}) = {AND f c | c | CONJ_OF c (fs DELETE f)}` by metis_tac[SET_TO_LIST_INV] >>
       `equiv0 μ (lit_list_to_form2 (MAP (λa. AND f a) (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)})))
       (lit_list_to_form2
       (SET_TO_LIST {AND f c | c | CONJ_OF c (fs DELETE f)}))` by metis_tac[lit_list_to_form2_SYM] >>
       `equiv0 μ (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)}))
       TRUE` by metis_tac[ALL_POSSIBLE_VALUE_TRUE] >>
       `equiv0 μ (AND f (lit_list_to_form2 (SET_TO_LIST {c | CONJ_OF c (fs DELETE f)}))) (AND f TRUE)` by metis_tac[equiv0_AND_subst] >>
       `equiv0 μ (AND f TRUE) f` by metis_tac[equiv0_TRUE_absorb] >>
       metis_tac[equiv0_SYM,equiv0_TRANS]));
  

(* stuff regarding the negation case *)

val lsatis_def = Define`
lsatis M w (f, b) <=> satis M w f = b`;

val csatis_def = Define`
csatis M w c <=> !l. l IN c ==> lsatis M w l`;

val dsatis_def = Define`
dsatis M w cs <=> ?c. c IN cs /\ csatis M w c`;

val is_lset_def = Define`
is_lset (c :'a # bool -> bool) fs <=> FINITE fs /\ FINITE c /\ CARD c = CARD fs /\ IMAGE FST c = fs`;
      
val CONJ_OF_lset = store_thm(
"CONJ_OF_lset",
``!c fs. CONJ_OF c fs ==> ?ls. is_lset ls fs /\
!M w. w IN M.frame.world ==> (csatis M w ls <=> satis M w c)``,
Induct_on `CONJ_OF` >> rw[]
>- (qexists_tac `{(c, T)}` >> rw[csatis_def,is_lset_def,lsatis_def])
>- (qexists_tac `{(c0, F)}` >> rw[csatis_def,is_lset_def,lsatis_def,satis_def])
>- (qexists_tac `(f0, T) INSERT ls` >> rw[csatis_def,is_lset_def,lsatis_def,satis_def,AND_def]
   >- fs[is_lset_def]
   >- fs[is_lset_def]
   >- (fs[is_lset_def] >> fs[EXTENSION] >>
      `(f0, T) NOTIN ls` by metis_tac[FST] >>
      fs[] >> `CARD fs <> 0` suffices_by decide_tac >>
      simp[] >> strip_tac >> fs[])
   >- fs[is_lset_def]
   >- (simp[DISJ_IMP_THM,FORALL_AND_THM] >> rw[lsatis_def] >> simp[GSYM csatis_def]))
>- (qexists_tac `(f0, F) INSERT ls` >> rw[csatis_def,is_lset_def,lsatis_def,satis_def,AND_def]
   >- fs[is_lset_def]
   >- fs[is_lset_def]
   >- (fs[is_lset_def] >> fs[EXTENSION] >>
      `(f0, F) NOTIN ls` by metis_tac[FST] >>
      fs[] >> `CARD fs <> 0` suffices_by decide_tac >>
      simp[] >> strip_tac >> fs[])
   >- fs[is_lset_def]
   >- (simp[DISJ_IMP_THM,FORALL_AND_THM] >> rw[lsatis_def] >> simp[GSYM csatis_def])));
   
val DISJ_OF0_cset = store_thm(
"DISJ_OF0_cset",
``!d fs. DISJ_OF0 d fs ==> !fs0. fs SUBSET {c | CONJ_OF c fs0} ==>
?cs. (!c. c IN cs ==> is_lset c fs0) /\
!M w. w IN M.frame.world ==> (satis M w d <=> ?c. c IN cs /\ csatis M w c)``,
Induct_on `DISJ_OF0` >> rw[]
>- (fs[SUBSET_DEF] >> pop_assum drule >> strip_tac >> drule CONJ_OF_lset >> rw[] >> qexists_tac `{ls}` >> fs[])
>- (`CONJ_OF f1 fs0` by (fs[SUBSET_DEF] >> metis_tac[]) >>
   drule CONJ_OF_lset >> rw[] >>
   `fs DELETE f1 ⊆ {c | CONJ_OF c fs0}` by fs[SUBSET_DEF] >>
   first_x_assum drule >> rw[] >>
   qexists_tac `ls INSERT cs` >> rw[] >> fs[] >> rw[satis_def] >> metis_tac[csatis_def]));

val DNF_OF_cset = store_thm(
  "DNF_OF_cset",
  ``!d fs. DNF_OF d fs ==>
           ?cs. (!c. c IN cs ==> is_lset c fs) /\
                !M w. w IN M.frame.world ==>
                      (satis M w d <=> ?c. c IN cs /\ csatis M w c)``,
  rw[DNF_OF_def, DISJ_OF_def]
  >- (qexists_tac `{}` >> simp[satis_def]) >>
  drule_then (qspec_then `fs` strip_assume_tac) DISJ_OF0_cset >> fs[] >>
  metis_tac[]);



val csatis_SUBSET = store_thm(
"csatis_SUBSET",
``!M w c. csatis M w c ==> !c0. c0 SUBSET c ==> csatis M w c0``,
rw[csatis_def,SUBSET_DEF]);



val is_lset_CONJ_OF_EXISTS = store_thm(
  "is_lset_CONJ_OF_EXISTS",
  ``!fs c. is_lset c fs /\ c <> {} ==>  ?f. (!M w. w IN M.frame.world ==> (satis M w f <=> csatis M w c)) /\ CONJ_OF f fs``,
csimp[is_lset_def] >>
`∀c. FINITE c ==> CARD c = CARD (IMAGE FST c) ∧ c ≠ ∅ ⇒
   ∃f.
      (∀M w. w ∈ M.frame.world ⇒ (satis M w f ⇔ csatis M w c)) ∧
      CONJ_OF f (IMAGE FST c)`
   suffices_by metis_tac[] >>
Induct_on `FINITE` >> rw[] >> Cases_on `e` >> fs[] >> Cases_on `c = {}`
>- (fs[] >> qexists_tac `if r then q else NOT q` >>
    simp[csatis_def, lsatis_def] >> rw[satis_def] >> metis_tac[CONJ_OF_cases])
>- (Cases_on `∃x. q = FST x ∧ x ∈ c`
  >- (`SUC (CARD c) = CARD (IMAGE FST c)` by fs[] >>
     `CARD (IMAGE FST c) > CARD c` by fs[] >>
     `CARD (IMAGE FST c) <= CARD c` by fs[CARD_IMAGE] >> fs[])
  >- (`SUC (CARD c) = SUC (CARD (IMAGE FST c))` by metis_tac[] >>
     `CARD c <> 0` by fs[] >>
     `CARD c = CARD (IMAGE FST c)` by fs[] >>
     first_x_assum drule >> rw[] >>
     Cases_on `r` >> rw[]
     >- (qexists_tac `AND q f` >> rw[]
        >- (eq_tac >> rw[]
	   >- (fs[satis_AND] >> rw[csatis_def,lsatis_def]
	      >- metis_tac[lsatis_def]
	      >- (`csatis M w c` by metis_tac[] >> metis_tac[csatis_def]))
	   >- (fs[satis_AND] >>
	       `{(q,T)} SUBSET ((q,T) INSERT c)` by fs[] >>
	       `csatis M w {(q,T)}` by metis_tac[csatis_SUBSET] >>
	       fs[csatis_def,lsatis_def]))
        >- (`(q INSERT IMAGE FST c) DELETE q = IMAGE FST c` by (fs[EXTENSION,DELETE_DEF,INSERT_DEF] >> metis_tac[]) >>
	   `q IN (q INSERT IMAGE FST c)` by fs[] >> metis_tac[CONJ_OF_cases]))
     >- (qexists_tac `AND (¬q) f` >> rw[]
        >- (eq_tac >> rw[]
	   >- (fs[satis_AND] >> rw[csatis_def,lsatis_def]
	      >- metis_tac[lsatis_def,satis_def]
	      >- (`csatis M w c` by metis_tac[] >> metis_tac[csatis_def]))
	   >- (fs[satis_AND] >>
	       `{(q,F)} SUBSET ((q,F) INSERT c)` by fs[] >>
	       `csatis M w {(q,F)}` by metis_tac[csatis_SUBSET] >>
	       fs[csatis_def,lsatis_def,satis_def]))
        >- (`(q INSERT IMAGE FST c) DELETE q = IMAGE FST c` by (fs[EXTENSION,DELETE_DEF,INSERT_DEF] >> metis_tac[]) >>
	   `q IN (q INSERT IMAGE FST c)` by fs[] >> metis_tac[CONJ_OF_cases])))));



val NEQ_lsets_FALSE = store_thm(
  "NEQ_lsets_FALSE",
  ``!c1 :('a form # bool) -> bool c2 fs. is_lset c1 fs /\ is_lset c2 fs /\ c1 <> c2 ==>
               !M w. w IN M.frame.world ==> ¬(csatis M w (c1 UNION c2))``,
  rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
  fs[EXTENSION] >>
  `?x. (x IN c1 /\ x NOTIN c2) \/ (x IN c2 /\ x NOTIN c1)` by metis_tac[] (* 2 *)
  >- (Cases_on `x'` >> Cases_on `r` (* 2 *)
     >- (`(q,F) IN c2` by
          (fs[is_lset_def,EXTENSION,IMAGE_DEF] >>
          `FST (q,T) = q` by fs[FST] >>
          `q IN fs` by metis_tac[] >>
	  `(∃x'. q = FST x' ∧ x' ∈ c2) ⇔ q ∈ fs` by metis_tac[] >>
          `(∃x'. q = FST x' ∧ x' ∈ c2)` by metis_tac[] >>
	  Cases_on `x'` >> `q' = q` by fs[FST] >> Cases_on `r` (* 2 *)
          >> metis_tac[]) >>
	fs[csatis_def] >>
	`lsatis M w (q,T) /\ lsatis M w (q,F)` by metis_tac[] >>
	metis_tac[lsatis_def,satis_def])
     >- (`(q,T) IN c2` by
          (fs[is_lset_def,EXTENSION,IMAGE_DEF] >>
          `FST (q,F) = q` by fs[FST] >>
          `q IN fs` by metis_tac[] >>
	  `(∃x'. q = FST x' ∧ x' ∈ c2) ⇔ q ∈ fs` by metis_tac[] >>
          `(∃x'. q = FST x' ∧ x' ∈ c2)` by metis_tac[] >>
	  Cases_on `x'` >> `q' = q` by fs[FST] >> Cases_on `r` (* 2 *)
          >> metis_tac[]) >>
	fs[csatis_def] >>
	`lsatis M w (q,T) /\ lsatis M w (q,F)` by metis_tac[] >>
	metis_tac[lsatis_def,satis_def]))
  >-  (Cases_on `x'` >> Cases_on `r` (* 2 *)
     >- (`(q,F) IN c1` by
          (fs[is_lset_def,EXTENSION,IMAGE_DEF] >>
          `FST (q,T) = q` by fs[FST] >>
          `q IN fs` by metis_tac[] >>
	  `(∃x'. q = FST x' ∧ x' ∈ c1) ⇔ q ∈ fs` by metis_tac[] >>
          `(∃x'. q = FST x' ∧ x' ∈ c1)` by metis_tac[] >>
	  Cases_on `x'` >> `q' = q` by fs[FST] >> Cases_on `r` (* 2 *)
          >> metis_tac[]) >>
	fs[csatis_def] >>
	`lsatis M w (q,T) /\ lsatis M w (q,F)` by metis_tac[] >>
	metis_tac[lsatis_def,satis_def])
     >- (`(q,T) IN c1` by
          (fs[is_lset_def,EXTENSION,IMAGE_DEF] >>
          `FST (q,F) = q` by fs[FST] >>
          `q IN fs` by metis_tac[] >>
	  `(∃x'. q = FST x' ∧ x' ∈ c1) ⇔ q ∈ fs` by metis_tac[] >>
          `(∃x'. q = FST x' ∧ x' ∈ c1)` by metis_tac[] >>
	  Cases_on `x'` >> `q' = q` by fs[FST] >> Cases_on `r` (* 2 *)
          >> metis_tac[]) >>
	fs[csatis_def] >>
	`lsatis M w (q,T) /\ lsatis M w (q,F)` by metis_tac[] >>
	metis_tac[lsatis_def,satis_def])));
     
   
val equiv0_negation_satis = store_thm(
    "equiv0_negation_satis",
    ``!f1 f2. equiv0 (μ:'b itself) f1 ¬f2 <=>
              (!M w:'b. w IN M.frame.world ==>
	            (satis M w f1 <=> satis M w ¬f2))``,
    rw[equiv0_def,satis_def] >> metis_tac[satis_in_world]);


val dsatis_ALL_POSSIBLE_VALUE = store_thm(
    "dsatis_ALL_POSSIBLE_VALUE",
    ``!fs. FINITE fs ==> fs <> {} ==> !M w. w IN M.frame.world ==> dsatis M w {c | is_lset c fs}``,
    Induct_on `FINITE fs` >> rw[] >>
    Cases_on `fs <> {}`
    >- (`∀M w. w ∈ M.frame.world ⇒ dsatis M w {c | is_lset c fs}` by metis_tac[] >>
       `dsatis M w {c | is_lset c fs}` by metis_tac[] >>
       fs[dsatis_def] >> Cases_on `satis M w e`
       >- (qexists_tac `(e,T) INSERT c` >> rw[] 
          >- (fs[is_lset_def] >> `(e,T) NOTIN c` suffices_by fs[] >> SPOSE_NOT_THEN ASSUME_TAC >>
	     `FST (e,T) = e` by fs[FST] >>
	     `e IN fs` by metis_tac[IMAGE_IN])
          >- (fs[csatis_def] >> metis_tac[lsatis_def]))
       >- (qexists_tac `(e,F) INSERT c` >> rw[] 
          >- (fs[is_lset_def] >> `(e,F) NOTIN c` suffices_by fs[] >> SPOSE_NOT_THEN ASSUME_TAC >>
	     `FST (e,F) = e` by fs[FST] >>
	     `e IN fs` by metis_tac[IMAGE_IN])
          >- (fs[csatis_def] >> metis_tac[lsatis_def])))
     >- (`fs = {}` by fs[] >> `e INSERT fs = {e}` by fs[] >> rw[] >> fs[dsatis_def] >>
        Cases_on `satis M w e`
	>- (qexists_tac `{(e,T)}` >> rw[]
	   >- fs[is_lset_def]
	   >- (fs[csatis_def] >> metis_tac[lsatis_def]))
        >- (qexists_tac `{(e,F)}` >> rw[]
	   >- fs[is_lset_def]
	   >- (fs[csatis_def] >> metis_tac[lsatis_def]))));
        
val dsatis_is_lset_complement = store_thm(
    "dsatis_is_lset_complement",
    ``!cs fs. FINITE fs /\ fs <> {} /\
             (!c. c IN cs ==> is_lset c fs) ==>
          (!M w. w IN M.frame.world ==>
	         (dsatis M w cs <=> ¬(dsatis M w ({c | is_lset c fs} DIFF cs))))``,
   rw[] >> eq_tac >> rw[]
   >- (fs[dsatis_def] >>
      `∀c'. (is_lset c' fs /\ c' NOTIN cs) ==> ¬csatis M w c'` suffices_by metis_tac[] >>
      SPOSE_NOT_THEN ASSUME_TAC >>
      fs[] >> `csatis M w (c UNION c')` by (fs[csatis_def]>> metis_tac[]) >>
      `is_lset c fs` by metis_tac[] >>
      `c <> c'` by metis_tac[] >> metis_tac[NEQ_lsets_FALSE])
   >- (fs[dsatis_def] >>
      `dsatis M w {c | is_lset c fs}` by metis_tac[dsatis_ALL_POSSIBLE_VALUE] >>
      fs[dsatis_def] >>
      metis_tac[]));

		   
		     
val satis_model_world_EXISTS = store_thm(
    "satis_model_world_EXISTS",
    ``!f. ¬(equiv0 (μ:'b itself) f FALSE) ==> ?M w:'b. satis M w f``,
    rw[equiv0_def] >> SPOSE_NOT_THEN ASSUME_TAC >> rw[] >> metis_tac[satis_def]);
    

val is_lset_DNF_OF_EXISTS = store_thm(
  "is_lset_DNF_OF_EXISTS",
  ``!s. FINITE s ==>
            !fs. FINITE fs /\ fs <> {} ==> (!c. c IN s ==> is_lset c fs) ==>
            ?f.
	       (!M w. w IN M.frame.world ==> (satis M w f <=> dsatis M w s)) /\
	       DNF_OF f fs``,
   Induct_on `FINITE s` >> rw[]
   >- (qexists_tac `FALSE` >> rw[]
      >- metis_tac[NOT_IN_EMPTY,satis_def,dsatis_def]
      >- rw[DNF_OF_def,DISJ_OF_def])
   >- (`∃f.
            (∀M w. w ∈ M.frame.world ⇒ (satis M w f ⇔ dsatis M w s)) ∧
            DNF_OF f fs` by metis_tac[] >>
      `is_lset e fs` by metis_tac[] >>
      `CARD fs <> 0` by metis_tac[CARD_EQ_0] >>
      `CARD e <> 0` by metis_tac[is_lset_def] >>
      `FINITE e` by metis_tac[is_lset_def] >>
      `e <> {}` by metis_tac[CARD_EQ_0] >>
      drule is_lset_CONJ_OF_EXISTS >> rw[] >>
      `f = FALSE \/ DISJ_OF0 f {c | CONJ_OF c fs}` by metis_tac[DNF_OF_def,DISJ_OF_def]
      >- (qexists_tac `f'` >> rw[] (* 2 *)
         >- (`(satis M w ⊥ ⇔ dsatis M w s)` by metis_tac[] >>
	    `¬(dsatis M w s)` by metis_tac[satis_def] >>
	    rw[dsatis_def] >>
	    `!c. c IN s ==> ¬(csatis M w c)` by metis_tac[dsatis_def] >>
	    metis_tac[])
	 >- (rw[DNF_OF_def,DISJ_OF_def] >>
	    fs[Once DISJ_OF0_cases]))
      >- (Cases_on `equiv0 μ f' FALSE` 
        >- (qexists_tac `f` >> rw[] >> fs[dsatis_def] >> eq_tac >> rw[]
	    >- metis_tac[]
	    >- (`satis M w f'` by metis_tac[] >>
	       `satis M w FALSE` by metis_tac[equiv0_def] >>
	       metis_tac[satis_def])
	    >- metis_tac[])
	>- (qexists_tac `DISJ f' f` >> rw[]
         >- (eq_tac >> rw[]
	    >- (`satis M w f' \/ satis M w f` by metis_tac[satis_def] (* 2 *)
	       >- (`csatis M w e` by metis_tac[] >>
	          fs[dsatis_def] >> qexists_tac `e` >> metis_tac[])
	       >- (`dsatis M w s` by metis_tac[] >>
	          fs[dsatis_def] >> qexists_tac `c` >> metis_tac[]))
            >- (fs[dsatis_def]
	       >> metis_tac[satis_def]))
	 >- (rw[DNF_OF_def,DISJ_OF_def,Once DISJ_OF0_cases] >>
	    `DISJ_OF0 f ({c | CONJ_OF c fs} DELETE f')` suffices_by metis_tac[] >>
	    SPOSE_NOT_THEN ASSUME_TAC >>
	    `f' IN {c | CONJ_OF c fs}` by fs[] >>
	    `?p. DISJ_OF p ({c | CONJ_OF c fs} DELETE f') /\ equiv0 μ f (DISJ f' p)` by metis_tac[DISJ_OF0_split] >>
	    `∀M w. w IN M.frame.world ==> (satis M w f ⇔ satis M w (DISJ f' p))` by metis_tac[equiv0_def] >>
	    `?M w. w IN M.frame.world /\ (satis M w f' /\ ¬(satis M w f))` suffices_by metis_tac[satis_def] >>
	    `?M w. w IN M.frame.world /\ csatis M w e /\ ¬(dsatis M w s)` suffices_by metis_tac[] >>
	    `?M w. satis M w f'` by metis_tac[satis_model_world_EXISTS] >>
	    map_every qexists_tac [`M`, `w`] >>
	    `w IN M.frame.world` by metis_tac[satis_in_world] >>
	    `csatis M w e` by metis_tac[] >> rw[]
	    >> SPOSE_NOT_THEN ASSUME_TAC >>
	       fs[dsatis_def] >>
	       `csatis M w (c UNION e)` by (fs[csatis_def] >> metis_tac[]) >>
	       `is_lset c fs` by metis_tac[] >>
	       `c <> e` by (SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[]) >> metis_tac[NEQ_lsets_FALSE])))));
	    
val EQ_equiv0_def = store_thm(
    "EQ_equiv0_def",
    ``!f g. equiv0 (μ:'b itself) f g <=> !M w:'b. w IN M.frame.world ==> (satis M w f <=> satis M w g)``,
    rw[equiv0_def] >> eq_tac >> rw[] >>
    Cases_on `w IN M.frame.world`
    >- metis_tac[]
    >- (`satis M w f = F` by metis_tac[satis_in_world] >>
       `satis M w g = F` by metis_tac[satis_in_world] >> metis_tac[]));

val FINITE_is_lset = store_thm(
    "FINITE_is_lset",
    ``!fs. FINITE fs ==> FINITE {c | is_lset c fs}``,
    rw[] >>
    `FINITE {T;F}` by fs[] >>
    `FINITE (fs CROSS {T;F})` by fs[FINITE_CROSS] >>
    `FINITE (POW (fs CROSS {T;F}))` by fs[FINITE_POW] >>
    `{c | is_lset c fs} SUBSET (POW (fs × {T; F}))` suffices_by metis_tac[SUBSET_FINITE] >>
    rw[SUBSET_DEF,POW_DEF] >> fs[is_lset_def] >> metis_tac[IMAGE_IN]);

val IBC_DNF_EXISTS_case3 = store_thm(
  "IBC_DNF_EXISTS_case3",
  ``!p fs. DNF_OF p fs /\ FINITE fs /\ fs <> {} ==>
           ?f. DNF_OF f fs /\ equiv0 μ (¬p) f``,
  rw[] >>
  drule DNF_OF_cset >> strip_tac >> 
  Cases_on `cs = {c | is_lset c fs}` 
  >- (qexists_tac `FALSE` >> rw[DNF_OF_def,DISJ_OF_def] >>
  `!M w. w IN M.frame.world ==> (satis M w (¬p) <=> satis M w FALSE)` suffices_by metis_tac[EQ_equiv0_def] >> rw[] >>
  `dsatis M w {c | is_lset c fs}` by metis_tac[dsatis_ALL_POSSIBLE_VALUE] >>
  `satis M w p` by metis_tac[dsatis_def] >>
  `satis M w (¬p) = F` by metis_tac[satis_def] >>
  `satis M w FALSE = F` by metis_tac[satis_def] >>
  metis_tac[])
  >- (`FINITE {c | is_lset c fs}` by metis_tac[FINITE_is_lset] >>
  `FINITE ({c | is_lset c fs} DIFF cs)` by fs[FINITE_DIFF] >>
  `({c | is_lset c fs} DIFF cs) <> {}` by (fs[DIFF_DEF,EXTENSION] >> SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[]) >>
  `cs SUBSET {c | is_lset c fs}` by fs[SUBSET_DEF] >>
  `!a. a IN ({c | is_lset c fs} DIFF cs) ==> is_lset a fs` by fs[DIFF_DEF] >>
  `∃f.
           (∀M w:'b. w ∈ M.frame.world ⇒ (satis M w f ⇔ dsatis M w ({c | is_lset c fs} DIFF cs))) ∧
           DNF_OF f fs` by (irule is_lset_DNF_OF_EXISTS >> fs[]) >>
  qexists_tac `f` >> rw[] >>
  `!M w. w IN M.frame.world ==> (satis M w (¬p) <=> satis M w f)` suffices_by metis_tac[EQ_equiv0_def] >> rw[] >>
  `satis M w p ⇔ dsatis M w cs` by metis_tac[dsatis_def] >>
  `satis M w f ⇔ dsatis M w ({c | is_lset c fs} DIFF cs)` by metis_tac[] >>
  `dsatis M w cs ⇔ ¬dsatis M w ({c | is_lset c fs} DIFF cs)` by metis_tac[dsatis_is_lset_complement] >>
  metis_tac[satis_def]));

val IBC_DNF_EXISTS = store_thm(
"IBC_DNF_EXISTS",
``!f fs. IBC f fs ==> FINITE fs /\ fs <> {} ==> ?p. DNF_OF p fs /\ equiv0 μ f p``,
Induct_on `IBC` >> rw[]
>- (`∃p. DNF_OF p fs ∧ equiv0 μ f p` by metis_tac[] >>
    `∃p'. DNF_OF p' fs ∧ equiv0 μ f' p'` by metis_tac[] >>
    `?t. DNF_OF t fs /\ equiv0 μ t (DISJ p p')` by metis_tac[DNF_OF_DISJ_equiv0] >> qexists_tac `t` >> rw[] >>
    fs[equiv0_def,satis_def])
>- (qexists_tac `FALSE` >> rw[] >> rw[DNF_OF_def,DISJ_OF_def])
>- (`∃p. DNF_OF p fs ∧ equiv0 μ f p` by metis_tac[] >>
   `?t. DNF_OF t fs /\ equiv0 μ (¬p) t` by metis_tac[IBC_DNF_EXISTS_case3] >>
   qexists_tac `t` >> rw[] >>
   fs[equiv0_def,satis_def] >> metis_tac[satis_in_world])
>- metis_tac[IBC_DNF_EXISTS_case4]);

val _ = export_theory();
