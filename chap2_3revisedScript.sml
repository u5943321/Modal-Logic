open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open equiv_on_partitionTheory;
open prop2_29Theory;
open prim_recTheory;
open listTheory pairTheory;

val _ = new_theory "chap2_3revised";

val irule = fn th => irule th >> rpt conj_tac

(* finite model property via selection *)






Theorem prop_letters_FINITE:
!phi. FINITE (prop_letters phi)
Proof
Induct_on `phi` >> rw[prop_letters_def]
QED

Theorem BIGCONJ_prop_letters_DEG:
∀s.
         FINITE s ⇒
         ∀n s0.
             (∀f. f ∈ s ⇒ DEG f ≤ n) ∧
             (∀f. f ∈ s ⇒ prop_letters f ⊆ s0) ⇒
             ∃ff.
                 DEG ff ≤ n ∧ prop_letters ff ⊆ s0 ∧
                 ∀w M.
                     w ∈ M.frame.world ⇒
                     (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `TRUE` >> rw[TRUE_def,satis_def,DEG_def,prop_letters_def]) >>
`(∀f. f ∈ s ⇒ DEG f ≤ n) ∧
 (∀f. f ∈ s ⇒ prop_letters f ⊆ s0)` by metis_tac[] >>
first_x_assum drule_all >> strip_tac >>
qexists_tac `AND e ff` >> 
rw[AND_def,satis_AND,DEG_def,prop_letters_def] >> metis_tac[]
QED



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


Theorem rooted_model_same_frame:
!M M' x. M.frame = M'.frame ==>
         (rooted_model M x M <=> rooted_model M' x M')
Proof
rw[rooted_model_def]
QED

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix(NONASSOC, 1900),
                  pp_elements = [TOK "//E", BreakSpace(1,0)],
                  term_name = "part_equiv"}
val _ = overload_on ("part_equiv", ``\s tyi. partition (equiv0 tyi) s``);


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
  (* done with the first paragraph *)
qabbrev_tac `s = prop_letters phi` >>
`FINITE s`
  by metis_tac[Abbr`s`,prop_letters_FINITE] >>
`INFINITE univ(:'b list)` by metis_tac[INFINITE_LIST_UNIV] >>
FREEZE_THEN drule
  (prop_2_29_prop_letters |> INST_TYPE [beta |-> ``:'b list``]) >> 
strip_tac >>
qabbrev_tac 
  `distfp = {f | DEG f ≤ k ∧ prop_letters f ⊆ s}//E (:β list)` >>
`FINITE distfp` by metis_tac[] >>
`FINITE (IMAGE CHOICE distfp)` 
  by metis_tac[FINITE_BIJ,CHOICE_BIJ_partition,equiv0_equiv_on] >>
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
   by 
    (rw[Abbr`W4`,Abbr`ss`,SUBSET_DEF] >> Cases_on `i` (* 2 *)
     >- fs[PRIM_REC_THM,Abbr`M3'`]
     >- (fs[PRIM_REC_THM] >>
         `?u. M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'`            by metis_tac[satis_def] >>
         `u IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧
                    satis M3' u phi'}` by fs[] >>
         `{u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}          <> {}`
           by metis_tac[MEMBER_NOT_EMPTY] >>
         `(CHOICE 
             {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧
                  satis M3' u phi'})
          IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧
                  satis M3' u phi'}`
           by metis_tac[CHOICE_DEF] >> fs[])) >>
(*proved W4 is subset of M3'*)
(* height ss issue *)
`!i a. a IN ss i ==> height M3' w2 M3' a = i`
  by
   (Induct_on `i` >> rw[] (* 2 *)
    >- (fs[Abbr`ss`,PRIM_REC_THM] >>
        `tree (hrestriction M2 w2 M2 k).frame w2` 
          by metis_tac[tree_hrestriction_tree] >>
        `rooted_model M3 w2 M3` 
          by metis_tac[Abbr`M3`,tree_like_model_rooted] >>
        `rooted_model M3' w2 M3'` by metis_tac[rooted_model_same_frame] >>
        metis_tac[root_height_0])
    >- (fs[Abbr`ss`,PRIM_REC_THM] >>
        `height M3' w2 M3' v = i` by metis_tac[] >>
        `{u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ satis M3' u phi'}          <> {}`
          by
           (fs[satis_def] >>
            rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `v'` >> rw[]) >>
        `(CHOICE
          {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ 
               satis M3' u phi'}) IN
          {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ 
               satis M3' u phi'}` by metis_tac[CHOICE_DEF] >>
        `!c.
           c IN {u | M3'.frame.rel v u ∧ u ∈ M3'.frame.world ∧ 
                     satis M3' u phi'}
              ==> height M3' w2 M3' c = SUC i`
          suffices_by metis_tac[] >> rw[] >>
        simp[ADD1] >>
        `tree (hrestriction M2 w2 M2 k).frame w2` by metis_tac[tree_hrestriction_tree] >>
        `tree M3.frame w2` by fs[Abbr`M3`] >>
        `tree M3'.frame w2` by metis_tac[] >>
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
      by (rw[IMAGE_DEF,SUBSET_DEF] >> fs[Abbr`bigset`] >> 
          simp[PULL_EXISTS] >>
          map_every qexists_tac [`(v,DIAM phi')`,`s'`] >>
          rw[] >> rw[Abbr`ff`] >> rw[EQ_IMP_THM,EXTENSION] (* 4 *)
          >- (qexists_tac `phi'` >> rw[])
          >- rw[]
          >- rw[]
          >- (`◇ phi' = ◇ phi''` by metis_tac[] >>
              metis_tac[DIAM_EQ_lemma])) >>
        (*subset proof end*)
    `FINITE
      (PRIM_REC {w2} sf i ×
         (IMAGE CHOICE 
        ((IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp) DELETE {})))`
      suffices_by metis_tac[SUBSET_FINITE,IMAGE_FINITE] >>
    irule FINITE_CROSS (* 2 *)
    >- rw[] >>
    `FINITE distfp` by metis_tac[] >>
    `FINITE (IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp)` 
      by metis_tac[IMAGE_FINITE] >>
    `FINITE 
     ((IMAGE (\s. s INTER {d | ?d0. d = DIAM d0}) distfp) DELETE {})` 
      by fs[] >>
    metis_tac[IMAGE_FINITE])
(*finiteness proof end*)
(*w2 IN M4.frame.world*)
>- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> qexists_tac `0` >> 
    fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
(*in M4.frame.world proof end*)
(* the following is the critical part, prove satis M4 w2 phi *)
>- (`?f. nbisim M4 M3' f k w2 w2`
         suffices_by
          (rw[] >> `DEG phi <= k` by fs[Abbr`k`] >>
           metis_tac[prop_2_31_half1]) >>
    qexists_tac 
      `\n a1 a2. a1 IN M4.frame.world /\ a2 IN M3'.frame.world /\
                 height M3' w2 M3' a1 = height M3' w2 M3' a2 /\
                 height M3' w2 M3' a1 <= k - n /\
                 (!phi. (DEG phi <= n /\ prop_letters phi ⊆ s)
                     ==> (satis M3' a1 phi <=> satis M3' a2 phi))` >>
    rw[nbisim_def] (* 8 *)
    >- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> 
        qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (`w2 IN M4.frame.world` suffices_by fs[Abbr`M4`,SUBSET_DEF] >>
        fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> 
        qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> 
        qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    >- (`w2 IN M4.frame.world` suffices_by fs[Abbr`M4`,SUBSET_DEF] >>
        fs[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >> 
        qexists_tac `0` >> fs[] >> simp[Abbr`ss`,PRIM_REC_THM])
    (*the four trivial subgoal solved*)
    >- (* height M3 w2 M3 w2 = 0 *)
       (`tree (hrestriction M2 w2 M2 k).frame w2` 
          by metis_tac[tree_hrestriction_tree] >>
        `rooted_model M3 w2 M3` 
          by metis_tac[Abbr`M3`,tree_like_model_rooted] >>
        `rooted_model M3' w2 M3'` 
          by metis_tac[rooted_model_same_frame] >>
        metis_tac[root_height_0])
    >- (`DEG (VAR p) = 0` by fs[DEG_def] >>
        first_x_assum drule >> strip_tac >> fs[prop_letters_def] >>
        Cases_on `p IN s` (* 2 *)
        >- (`satis M3' a1 (VAR p) <=> satis M3' a2 (VAR p)` 
              by metis_tac[] >>
            `satis M4 a1 (VAR p) ⇔ satis M3' a1 (VAR p)` 
              suffices_by metis_tac[] >>
            rw[satis_def,Abbr`M4`] >> fs[satis_def] >>
            metis_tac[SUBSET_DEF]) >>
        rw[satis_def,Abbr`M4`,Abbr`M3'`,Abbr`s`] >> fs[])
    (*remains two Hennessy-Milner style subgoal*)
    >- (SPOSE_NOT_THEN ASSUME_TAC >>
        `?phi. DEG phi ≤ n + 1 /\
               prop_letters phi  ⊆ s /\
               (satis M3' a1 phi /\ ¬satis M3' a2 phi)` 
          suffices_by metis_tac[] >>
        `tree (hrestriction M2 w2 M2 k).frame w2`
          by metis_tac[tree_hrestriction_tree] >>
        `tree M3.frame w2` by rw[Abbr`M3`] >>
        `tree M3'.frame w2` by metis_tac[] >>
        `!a2'. a2' IN M3'.frame.world /\ M3'.frame.rel a2 a2' ==>
               height M3' w2 M3' a1' = height M3' w2 M3' a2' /\ 
               height M3' w2 M3' a2' ≤ k − n`
           by
            (rw[] (* 2 *)
             >- (`height M3' w2 M3' a2' = height M3' w2 M3' a2 + 1` 
                   by metis_tac[tree_height_rel_lemma] >>
                 `a1 IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                 `a1' IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                 `M3'.frame.rel a1 a1'` by fs[Abbr`M4`,Abbr`M3'`] >>
                 `height M3' w2 M3' a1' = height M3' w2 M3' a1 + 1` 
                   by metis_tac[tree_height_rel_lemma] >>
                 fs[])
             >- (`height M3' w2 M3' a2' = height M3' w2 M3' a2 + 1` by metis_tac[tree_height_rel_lemma] >>
                 fs[])) >>
        `∀a2'.
          a2' ∈ M3'.frame.world ⇒
          M3'.frame.rel a2 a2' ⇒
          ∃phi. DEG phi ≤ n ∧
                prop_letters phi ⊆ s /\
                (satis M3' a1' phi /\ ¬satis M3' a2' phi)`
          by
           (rw[] >>
            `∃phi. DEG phi ≤ n ∧
             prop_letters phi ⊆ s /\
             (satis M3' a1' phi ⇎ satis M3' a2' phi)` by metis_tac[] >>
            Cases_on `satis M3' a1' phi'` (* 2 *)
            >- (qexists_tac `phi'` >> metis_tac[satis_def])
            >- (qexists_tac `NOT phi'` >> rw[] (* 4 *)
                >- fs[DEG_def]
                >- fs[Abbr`s`,prop_letters_def]
                >- (`M4.frame.world SUBSET M3'.frame.world`
                      by fs[Abbr`M4`] >>
                    `a1' IN M3'.frame.world` by fs[SUBSET_DEF] >>
                    metis_tac[satis_def])
                >- (`satis M3' a2' phi'` by metis_tac[] >> 
                    metis_tac[satis_def]))) >>
        (*big by tactic end*)
        qabbrev_tac
        `phis = {phi | ∃a2'. a2' ∈ M3'.frame.world ∧
                             M3'.frame.rel a2 a2' ∧ DEG phi ≤ n ∧
                             prop_letters phi ⊆ s /\
                             satis M3' a1' phi ∧ ¬satis M3' a2' phi}` >>
        qabbrev_tac 
         `rs = IMAGE CHOICE 
                     ((IMAGE (\s. s INTER phis) distfp) DELETE {})` >>
        `FINITE rs`
            by (`FINITE (IMAGE (λs. s ∩ phis) distfp)` 
                  by metis_tac[IMAGE_FINITE] >>
                `FINITE ((IMAGE (λs. s ∩ phis) distfp) DELETE {})` 
                  by metis_tac[FINITE_DELETE] >>
                metis_tac[IMAGE_FINITE,Abbr`rs`]) >>
        `!f. f IN rs ==> DEG f <= n`
            by
             (rw[Abbr`rs`] >> 
              `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` 
                by metis_tac[CHOICE_DEF] >>
              `(CHOICE (s' ∩ phis)) IN phis` 
                by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
              fs[Abbr`phis`]) >>
        drule 
         (BIGCONJ_prop_letters_DEG |> 
          INST_TYPE [alpha |-> ``:'b list``]) >>
        rw[] >>
        `∀f. f ∈ rs ⇒ prop_letters f ⊆ s`
          by
           (rw[Abbr`rs`] >> fs[Abbr`distfp`,partition_def] >> rw[] >>
            `CHOICE
             ({y |
               (DEG y ≤ k ∧ prop_letters y ⊆ s) ∧ equiv0 (:β list) x y} ∩
              phis) IN
             ({y |
               (DEG y ≤ k ∧ prop_letters y ⊆ s) ∧ equiv0 (:β list) x y} ∩
              phis)` by metis_tac[CHOICE_DEF] >>
            fs[]) >>
        `∃ff.
           DEG ff ≤ n ∧
           prop_letters ff ⊆ s /\
           (∀(w:'b list) M.
               w ∈ M.frame.world ⇒
               (satis M w ff ⇔ ∀f. f ∈ rs ⇒ satis M w f))` 
          by metis_tac[] >>
        qexists_tac `DIAM ff` >> rw[] (* 4 *)
        >- fs[DEG_def]
        >- (fs[Abbr`s`,prop_letters_def])
        >- (rw[satis_def] (* 2 *)
            >- (fs[SUBSET_DEF,Abbr`M4`] >> metis_tac[Abbr`M4`])
            >- (qexists_tac `a1'` >> rw[] (* 3 *)
                >- fs[SUBSET_DEF,Abbr`M4`,Abbr`M3'`]
                >- fs[SUBSET_DEF,Abbr`M4`,Abbr`M3'`]
                >- (`a1' IN M3'.frame.world` by fs[Abbr`M4`,SUBSET_DEF] >>
                    `∀f. f ∈ rs ⇒ satis M3' a1' f` 
                      suffices_by metis_tac[] >>
                    rw[Abbr`rs`,IMAGE_DEF] >>
                    `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` 
                      by metis_tac[CHOICE_DEF] >>
                    `(CHOICE (s' ∩ phis)) IN phis` by
                      metis_tac[INTER_SUBSET,SUBSET_DEF] >>
                    fs[Abbr`phis`])))
        >- (rw[satis_def] >>
            `!v. M3'.frame.rel a2 v /\ v IN M3'.frame.world
                 ==> ¬satis M3' v ff` 
              suffices_by metis_tac[] >>
            rw[] >>
            `∃phi. DEG phi ≤ n ∧ prop_letters phi ⊆ s /\
                   satis M3' a1' phi ∧ ¬satis M3' v phi` by metis_tac[] >>
            `equiv0 (:β list) equiv_on 
              {f | DEG f ≤ k /\ prop_letters f ⊆ s}`
              by metis_tac[equiv0_equiv_on] >>
            `BIGUNION (partition (equiv0 (:β list)) 
                      {f | DEG f ≤ k /\ prop_letters f ⊆ s})
             = {f | DEG f ≤ k /\ prop_letters f ⊆ s}` by
              metis_tac[BIGUNION_partition] >>
            fs[BIGUNION] >> `n <= k` by fs[] >>
            `DEG phi' <= k` by fs[] >>
            `phi' IN {f | DEG f ≤ k /\ prop_letters f ⊆ s}` by fs[] >>
            `phi' IN
              {x | ∃s'. s' ∈ {f | DEG f ≤ k /\ prop_letters f ⊆ s}//E (:β list) ∧                    x ∈ s'}`
               by metis_tac[] >> fs[] >>
            qexists_tac `CHOICE (s' INTER phis)` >> rw[] (* 2 *)
            >- (rw[Abbr`rs`,IMAGE_DEF] >> simp[PULL_EXISTS] >> 
                qexists_tac `s'` >> rw[] (* 2 *)
                >- fs[Abbr`distfp`]
                >- (`phi' IN phis` by (fs[Abbr`phis`] >>
                    qexists_tac `v` >> rw[]) >>
                    `phi' IN (s' ∩ phis)` by metis_tac[IN_INTER] >>
                     metis_tac[MEMBER_NOT_EMPTY]))
            >- (`s' ∩ phis <> {}`
                  by 
                   (`phi' IN phis` by 
                      (fs[Abbr`phis`] >> qexists_tac `v` >> rw[]) >>
                    `phi' IN (s' ∩ phis)` by metis_tac[IN_INTER] >>
                    metis_tac[MEMBER_NOT_EMPTY]) >>
                `(CHOICE (s' ∩ phis)) IN (s' ∩ phis)` 
                  by metis_tac[CHOICE_DEF] >>
                `(CHOICE (s' ∩ phis)) IN s'` 
                  by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
                `equiv0 (:β list) phi' (CHOICE (s' ∩ phis))`
                  by metis_tac[partition_elements_interrelate] >>
                fs[equiv0_def])))
    >- (qabbrev_tac
        `phis = {phi | DEG phi <= n /\
                       prop_letters phi ⊆ s /\
                       satis M3' a2' phi}` >>
        qabbrev_tac 
        `rs = IMAGE CHOICE 
                    ((IMAGE (\s. s INTER phis) distfp) DELETE {})` >>
        `FINITE rs`
            by (`FINITE (IMAGE (λs. s ∩ phis) distfp)` 
                  by metis_tac[IMAGE_FINITE] >>
               `FINITE ((IMAGE (λs. s ∩ phis) distfp) DELETE {})` 
                  by metis_tac[FINITE_DELETE] >>
               metis_tac[IMAGE_FINITE,Abbr`rs`]) >>
        `!f. f IN rs ==> DEG f <= n`
            by (rw[Abbr`rs`] >> 
                `(CHOICE (s' ∩ phis)) IN (s' INTER phis)`
                  by metis_tac[CHOICE_DEF] >>
                `(CHOICE (s' ∩ phis)) IN phis` 
                  by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
               fs[Abbr`phis`]) >>
        `∀f. f ∈ rs ⇒ prop_letters f ⊆ s`
          by
           (rw[Abbr`rs`] >> fs[Abbr`distfp`,partition_def] >> rw[] >>
            `CHOICE
             ({y |
               (DEG y ≤ k ∧ prop_letters y ⊆ s) ∧ equiv0 (:β list) x y} ∩
              phis) IN
             ({y |
               (DEG y ≤ k ∧ prop_letters y ⊆ s) ∧ equiv0 (:β list) x y} ∩
              phis)` by metis_tac[CHOICE_DEF] >>
            fs[]) >>
        (*cheated! same point as above fixed*)
        drule (BIGCONJ_prop_letters_DEG |> 
               INST_TYPE [alpha |-> ``:'b list``]) >> rw[] >>
        `∃ff.
           DEG ff ≤ n ∧
           prop_letters ff ⊆ s /\
           (∀(w:'b list) M.
               w ∈ M.frame.world ⇒
               (satis M w ff ⇔ ∀f. f ∈ rs ⇒ satis M w f))`
          by metis_tac[] >>
        `satis M3' a2' ff`
            by (fs[] >> rw[Abbr`rs`] >>
               `(CHOICE (s' ∩ phis)) IN (s' INTER phis)` 
                 by metis_tac[CHOICE_DEF] >>
               `(CHOICE (s' ∩ phis)) IN phis` 
                 by metis_tac[INTER_SUBSET,SUBSET_DEF] >>
               fs[Abbr`phis`]) >>
        `satis M3' a2 (DIAM ff)`
            by (rw[satis_def] >> qexists_tac `a2'` >> rw[]) >>
        `DEG (DIAM ff) <= n + 1` by fs[DEG_def] >>
        `prop_letters (DIAM ff) ⊆ s` by fs[prop_letters_def] >>
        `satis M3' a1 (DIAM ff)` by metis_tac[] >>
        simp[Abbr`M4`,Abbr`W4`] >> simp[PULL_EXISTS] >>
        map_every qexists_tac
        [`CHOICE {u | M3'.frame.rel a1 u /\ satis M3' u ff}`,
         `height M3' w2 M3' a1 + 1`,`height M3' w2 M3' a1 + 1`] >>
        rw[] (* 6 *)
        >- (`(height M3' w2 M3' a2 + 1) = SUC (height M3' w2 M3' a2)` 
             by fs[] >>
            rw[Abbr`ss`,PRIM_REC_THM] >>
            qexists_tac `{u | M3'.frame.rel a1 u ∧ satis M3' u ff}` >>
            rw[] >> simp[PULL_EXISTS] >>
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
            `equiv0 (:β list) equiv_on {f | DEG f ≤ k /\ prop_letters f ⊆ s}`
              by metis_tac[equiv0_equiv_on] >>
            `BIGUNION (partition (equiv0 (:β list)) {f | DEG f ≤ k /\ 
                                                 prop_letters f ⊆ s}) =
             {f | DEG f ≤ k /\ prop_letters f ⊆ s}` 
              by metis_tac[BIGUNION_partition] >>
            fs[BIGUNION] >>
            `DEG (DIAM ff) <= k` by fs[DEG_def] >>
            (*`∀a. VAR a ∈ subforms (DIAM ff) ⇒ a ∈ s` by fs[subforms_def] >> *repeat?*)
            `(DIAM ff) IN {f | DEG f ≤ k ∧ prop_letters f ⊆ s}` by fs[] >>
            `(DIAM ff) IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ prop_letters f ⊆ s}//E (:β list) ∧
                               x ∈ s'}` by metis_tac[] >> fs[] >>
            qexists_tac `s''` >> rw[] >>
            `s'' ∩ {d | ∃d0. d = ◇ d0} <> {}`
               by (`(DIAM ff) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by fs[IN_INTER,IN_DEF] >>
                    metis_tac[MEMBER_NOT_EMPTY]) >>
            `(CHOICE (s'' ∩ {d | ∃d0. d = ◇ d0})) IN (s'' ∩ {d | ∃d0. d = ◇ d0})`
               by metis_tac[CHOICE_DEF] >>
            fs[] >> rw[] (* 4 *)
            >- (fs[equiv0_def,partition_def] >>
                `(◇ ff) ∈ {y | (DEG y ≤ k ∧ prop_letters y ⊆ s) ∧
                               ∀M w:β list. satis M w x ⇔ satis M w y}` 
                  by metis_tac[] >>
                fs[] >>
                `satis M3' a1 x` by metis_tac[] >> rw[] >>
                fs[])
            >- rw[Abbr`distfp`]
            >- (`height M3' w2 M3' a1 = i` by metis_tac[] >>
                fs[PULL_EXISTS])
            >- (`(DIAM d0) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` 
                 by metis_tac[CHOICE_DEF] >>
                `(DIAM d0) IN s''` by metis_tac[IN_INTER] >>
                fs[partition_def] >> rw[] >>
                fs[] >>
                `equiv0 (:β list) (DIAM ff) (DIAM d0)` by metis_tac[equiv0_def] >>
                `INFINITE univ(:'b list)` 
                  by metis_tac[INFINITE_LIST_UNIV] >>
                `equiv0 (:β list) ff d0` by metis_tac[equiv0_DIAM] >>
                fs[equiv0_def] >> rw[Once EXTENSION,Once EQ_IMP_THM] >> 
                metis_tac[satis_in_world]))
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
     qexists_tac `{u | M3'.frame.rel a1 u ∧ satis M3' u ff}` >>
     rw[] >> simp[PULL_EXISTS] >>
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
     `equiv0 (:β list) equiv_on {f | DEG f ≤ k /\ prop_letters f ⊆ s}` 
       by metis_tac[equiv0_equiv_on] >>
     `BIGUNION 
       (partition (equiv0 (:β list)) {f | DEG f ≤ k /\ prop_letters f ⊆ s}) =
      {f | DEG f ≤ k /\ prop_letters f ⊆ s}` 
      by metis_tac[BIGUNION_partition] >>
     fs[BIGUNION] >>
     `DEG (DIAM ff) <= k` by fs[DEG_def] >>
     `prop_letters (DIAM ff) ⊆ s` by fs[prop_letters_def] >>
     `(DIAM ff) IN {f | DEG f ≤ k /\ prop_letters f ⊆ s}` by fs[] >>
     `(DIAM ff) IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ prop_letters f ⊆ s}//E (:β list) ∧
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
         fs[])
     >- rw[Abbr`distfp`]
     >- (`height M3' w2 M3' a1 = i` by metis_tac[] >>
         fs[PULL_EXISTS])
     >- (`(DIAM d0) IN (s'' ∩ {d | ∃d0. d = ◇ d0})` by metis_tac[CHOICE_DEF] >>
         `(DIAM d0) IN s''` by metis_tac[IN_INTER] >>
         fs[partition_def] >> rw[] >>
         fs[] >>
         `equiv0 (:β list) (DIAM ff) (DIAM d0)` by metis_tac[equiv0_def] >>
         `INFINITE univ(:'b list)` by metis_tac[INFINITE_LIST_UNIV] >>
         `equiv0 (:β list) ff d0` by metis_tac[equiv0_DIAM] >>
         fs[equiv0_def] >> rw[Once EXTENSION,Once EQ_IMP_THM] >> metis_tac[satis_in_world]))
(* 4th out of 6 *)
>- (fs[satis_def] >>
    `{u | M3'.frame.rel a1 u ∧ satis M3' u ff} <> {}`
      by
       (`?u. u IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >> 
    qexists_tac `v'` >> rw[]) >>
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
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >> 
    qexists_tac `v'` >> rw[]) >>
    `(CHOICE {u | M3'.frame.rel a1 u ∧ satis M3' u ff}) IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}`
      by metis_tac[CHOICE_DEF] >>
    `!c. c IN {u | M3'.frame.rel a1 u ∧ satis M3' u ff}  ==> (satis M3' c phi' ⇔ satis M3' a2' phi')`
      suffices_by metis_tac[] >> rw[] >>
    SPOSE_NOT_THEN ASSUME_TAC >> Cases_on `satis M3' c phi'` (* 2 *)
    >- (`¬satis M3' a2' phi'` by metis_tac[] >>
        `satis M3' a2' (NOT phi')` by metis_tac[satis_def] >>
        `(NOT phi') IN phis` by 
          (fs[Abbr`phis`] >> fs[DEG_def,prop_letters_def]) >>
        `?r. r IN rs /\ equiv0 (:β list) r (NOT phi')`
         by
          (`DEG (NOT phi') <= n` by fs[DEG_def] >>
           `equiv0 (:β list) equiv_on {f | DEG f ≤ k /\ prop_letters f ⊆ s}`
             by metis_tac[equiv0_equiv_on] >>
           `BIGUNION (partition (equiv0 (:β list)) 
               {f | DEG f ≤ k /\ prop_letters f ⊆ s}) =
            {f | DEG f ≤ k /\ prop_letters f ⊆ s}`
             by metis_tac[BIGUNION_partition] >>
           fs[BIGUNION] >> `n <= k` by fs[] >>
           `DEG (NOT phi') <= k` by fs[] >>
           `(NOT phi') IN {f | DEG f ≤ k /\ prop_letters f ⊆ s}` 
             by fs[prop_letters_def] >>
           `(NOT phi') IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧ prop_letters f ⊆ s}//E (:β list) ∧
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
               `!f. f IN (s' ∩ phis) ==> equiv0 (:β list) f (¬phi')` suffices_by metis_tac[] >> rw[] >>
               fs[partition_def] >> rw[] >>
               fs[] >>
               fs[equiv0_def])) (* by tactic ends *) >>
        `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
        `satis M3' c r` by metis_tac[] >>
        `satis M3' c (NOT phi')` by metis_tac[equiv0_def] >> metis_tac[satis_def])
    >- (`satis M3' a2' phi'` by metis_tac[] >>
        `phi' IN phis` by fs[Abbr`phis`] >>
        `?r. r IN rs /\ equiv0 (:β list) r phi'` by
          (`equiv0 (:β list) equiv_on {f | DEG f ≤ k /\ prop_letters f ⊆ s}`
             by metis_tac[equiv0_equiv_on] >>
           `BIGUNION (partition (equiv0 (:β list)) {f | DEG f ≤ k /\ prop_letters f ⊆ s}) =
            {f | DEG f ≤ k /\ prop_letters f ⊆ s}` by metis_tac[BIGUNION_partition] >>
        fs[BIGUNION] >> `n <= k` by fs[] >>
        `DEG phi' <= k` by fs[] >>
        `phi' IN {f | DEG f ≤ k ∧  prop_letters f ⊆ s}` by fs[] >>
        `phi' IN {x | ∃s'. s' ∈ {f | DEG f ≤ k ∧  prop_letters f ⊆ s}//E (:β list) ∧
                               x ∈ s'}` by metis_tac[] >> fs[] >>
        rw[Abbr`rs`] >> simp[PULL_EXISTS] >> qexists_tac `s'` >> rw[] (* 3 *)
        >- rw[Abbr`distfp`]
        >- (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `phi'` >>
            metis_tac[IN_INTER])
        >- (`s' ∩ phis ≠ ∅` by
             (`?p. p IN s' ∩ phis` suffices_by metis_tac[MEMBER_NOT_EMPTY] >> qexists_tac `phi'` >>
              metis_tac[IN_INTER]) >>
            `CHOICE (s' ∩ phis) IN (s' ∩ phis)` by metis_tac[CHOICE_DEF] >>
            `!f. f IN (s' ∩ phis) ==> equiv0 (:β list) f (phi')` suffices_by metis_tac[] >> rw[] >>
            fs[partition_def] >> rw[] >> fs[] >>
            fs[equiv0_def])) (* by tactic ends *) >>
        `c IN M3'.frame.world` by metis_tac[satis_in_world] >>
        `satis M3' c r` by metis_tac[] >>
        `satis M3' c phi'` by metis_tac[equiv0_def]))))
QED

