open HolKernel Parse boolLib bossLib;
open ultrafilterTheory;
open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

val _ = ParseExtras.tight_equality()
val _ = new_theory "ultraproduct";

val Cart_prod_def = Define`
  Cart_prod I A = {f | !i. i IN I ==> f i IN A i}`;

val Uequiv_def = Define`
  Uequiv U I A f g <=> ultrafilter U I /\
                     (!i. i IN I ==> A i <> {}) /\
		     f IN Cart_prod I A /\ g IN Cart_prod I A /\
		     {i | i IN I /\ f i = g i} IN U`;

val prop_A_16 = store_thm(
  "prop_A_16",
  ``!U I A. ultrafilter U I ==> (Uequiv U I A) equiv_on Cart_prod I A``,
  rw[Uequiv_def,Cart_prod_def,equiv_on_def] (* 4 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- fs[EQ_SYM_EQ]
  >- (`{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} ⊆ {i | i ∈ I' ∧ x i = z i}` by rw[SUBSET_DEF,INTER_DEF,EXTENSION] >>
     `{i | i ∈ I' ∧ x i = z i} ⊆ I'` by rw[SUBSET_DEF] >>
     metis_tac[ultrafilter_def,proper_filter_def,filter_def]));




val ultraproduct_def = Define`
  ultraproduct U I A = partition (Uequiv U I A) (Cart_prod I A)`;


val models2worlds_def = Define`
  models2worlds MS = \i. (MS i).frame.world`;

val ultraproduct_model_def = Define`
  ultraproduct_model U I MS = <| frame := <| world := ultraproduct U I (models2worlds MS);
                                               rel := \fu gu. (?f g. f IN fu /\ g IN gu /\
					                      {i | i IN I /\ (MS i).frame.rel (f i) (g i)} IN U) |>;
			          valt := \p fu. (?f. f IN fu /\ {i | i IN I /\ (f i) IN (MS i).valt p} IN U) |>`;


val ultraproduct_world_NOT_EMPTY = store_thm(
  "ultraproduct_world_NOT_EMPTY",
  ``!U J MS v. ultrafilter U J ==> v IN (ultraproduct_model U J MS).frame.world ==> v <> {}``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def] >> metis_tac[prop_A_16,EMPTY_NOT_IN_partition]);

val ultraproduct_world = store_thm(
  "ultraproduct_world",
  ``!U J MS.
    ultrafilter U J ==>
       (!v.
           v ∈ (ultraproduct_model U J MS).frame.world <=>
               (!i. i IN J ==> (MS i).frame.world <> {}) /\
               (∃x.
                   (∀i. i ∈ J ⇒ x i ∈ (MS i).frame.world) /\
                   v = {y | (∀i. i ∈ J ⇒ y i ∈ (MS i).frame.world) /\ {i | i ∈ J ∧ x i = y i} ∈ U}))``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >> qexists_tac `x` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]);

  
val ultraproduct_rel = save_thm(
  "ultraproduct_rel",
  ``(ultraproduct_model U J MS).frame.rel w v``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])

val ultraproduct_valt = save_thm(
  "ultraproduct_valt",
  ``v IN (ultraproduct_model U J MS).valt p``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])



val ultraproduct_world_constant = store_thm(
  "ultraproduct_world_constant",
  ``!U J MS w.
  ultrafilter U J ⇒
  (∀i. i ∈ J ⇒ MS i = M) ⇒
  ({fw | Uequiv U J (models2worlds MS) (λi. w) fw} ∈ (ultraproduct_model U J MS).frame.world
  <=> w ∈ M.frame.world)``,
  rw[EQ_IMP_THM] 
  >- (`?i. i IN J`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY] >>
     `{fw | Uequiv U J (models2worlds MS) (λi. w) fw} <> {}`
       by metis_tac[ultraproduct_world_NOT_EMPTY] >> fs[ultraproduct_world] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `?a. a IN {fw |
       ultrafilter U J ∧ (∀i. i ∈ J ⇒ (MS i).frame.world ≠ ∅) ∧
       (∀i. i ∈ J ⇒ w ∈ (MS i).frame.world) ∧
       (∀i. i ∈ J ⇒ fw i ∈ (MS i).frame.world) ∧
       {i | i ∈ J ∧ w = fw i} ∈ U}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >> metis_tac[])
  >- (rw[ultraproduct_world] (* 2 *)
     >- metis_tac[MEMBER_NOT_EMPTY]
     >- (qexists_tac `\i.w` >> rw[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        simp[EXTENSION] >> metis_tac[])));



val ultrapower_valt_well_defined = store_thm(
  "ultrapower_valt_well_defined",
  ``!U J Ms. ultrafilter U J ==> !f g. Uequiv U J (models2worlds Ms) f g ==>
             ({i | i IN J /\ (f i) IN (Ms i).valt p} IN U <=>
	     {i | i IN J /\ (g i) IN (Ms i).valt p} IN U)``,
  rw[Uequiv_def,models2worlds_def,Cart_prod_def] >> eq_tac >> rw[]
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ g i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ g i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[])
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ f i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ f i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[]));


val Los_modal_thm = store_thm(
  "Los_modal_thm",
  ``!U J Ms. ultrafilter U J ==>
             !phi fc. fc IN (ultraproduct_model U J Ms).frame.world ==>
	              (satis (ultraproduct_model U J Ms) fc phi <=>
	              ?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U)``,
  strip_tac >> strip_tac >> strip_tac  >> strip_tac >> Induct_on `phi` >> rw[] (* 5 *)
(*-----------------------------block 1 `` VAR case``------------------------------------- *)
>- 
(fs[satis_def,ultraproduct_world,ultraproduct_valt] >> eq_tac >> rw[] (* 2 *)
>- (qexists_tac `f` >> rw[] >> fs[] >>
        `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt a} =
	{i | i IN J /\ f i IN (Ms i).valt a}` suffices_by metis_tac[] >>
	simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
	`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
         ?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
            fc =
            {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
	`f IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x' i = y i} IN U}`
	  by metis_tac[] >> fs[])
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
       fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
     by metis_tac[ultraproduct_world] >>
   fs[] >> qexists_tac `f` >> rw[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt a} = {i | i IN J /\ f i IN (Ms i).valt a}`
     by rw[EXTENSION,EQ_IMP_THM] >>
   metis_tac[]))
(*-----------------------------block 2 `` \/ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 3 *)
>- (qexists_tac `f` >> rw[] >> 
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (qexists_tac `f` >> rw[] >> 
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (`{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} =
        {i | i IN J /\ satis (Ms i) (f i) phi} ∪ {i | i IN J /\ satis (Ms i) (f i) phi'}`
	  by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ J /\
	 {i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ J` by fs[SUBSET_DEF] >>
	`{i | i IN J /\ satis (Ms i) (f i) phi} IN U \/
	{i | i IN J /\ satis (Ms i) (f i) phi'} IN U` by metis_tac[ultrafilter_UNION]
	>> metis_tac[]))
(*-----------------------------block 3 `` FALSE case``------------------------------------- *)
>-
(`((satis (ultraproduct_model U J Ms) fc FALSE) = F) /\
((?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) FALSE} IN U) = F)` suffices_by metis_tac[] >> rw[] (* 2 *)
>- rw[satis_def]
>- (`{i | i IN J /\ satis (Ms i) (f i) FALSE} NOTIN U` suffices_by metis_tac[] >>
   `{i | i IN J /\ satis (Ms i) (f i) FALSE} = {}`
     by rw[EXTENSION,EQ_IMP_THM,satis_def] >>
   metis_tac[EMPTY_NOTIN_ultrafilter]))
(*-----------------------------block 4 `` ¬ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   qexists_tac `x` >> rw[] (* 2 *)
   >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
   >- (`x IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
        by (rw[] >> metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} NOTIN U` by metis_tac[] >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
      `J DIFF {i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def] >>
      fs[DIFF_DEF] >>
      `{i | i IN J /\ x i IN (Ms i).frame.world /\ ~satis (Ms i) (x i) phi} =
      {x' | x' IN J /\ (x' NOTIN J \/ ~satis (Ms x') (x x') phi)}`
        by rw[EXTENSION,EQ_IMP_THM] >>
      metis_tac[]))
>- (`!f'. f' IN fc ==> {i | i IN J /\ satis (Ms i) (f' i) phi} NOTIN U` suffices_by metis_tac[] >> rw[] >>
   `(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   fs[] >>
   `{i | i IN J /\ satis (Ms i) (f' i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
   `J DIFF {i | i IN J /\ satis (Ms i) (f' i) phi} IN U` suffices_by metis_tac[ultrafilter_def] >>
   rw[DIFF_DEF] >>
   `{x | x IN J /\ (x NOTIN J \/ ~satis (Ms x) (f' x) phi)} =
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by rw[EXTENSION,EQ_IMP_THM] >> fs[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} ⊆
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by (rw[SUBSET_DEF] >> metis_tac[]) >>
   `{x | x IN J /\ ~satis (Ms x) (f' x) phi} ⊆ J` by rw[SUBSET_DEF] >>
   metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-----------------------------block 4 ``DIAM case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
(*-------------------------------half 1---------------------------------------------------*)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
   fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >> qexists_tac `x'` >> rw[] >> fs[] (* 2 *)
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- (`?f g.
      f IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x' i = y i} IN U} /\ g IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x i = y i} IN U} /\
      {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U` by metis_tac[ultraproduct_rel] >> fs[] >>
     `{i | i IN J /\ x' i = f i} ∩ {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ x' i = f i} INTER {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} ⊆ {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} `
       by rw[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ⊆ J` by fs[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by (`?r. r IN {y |
          (!i. i IN J ==> y i IN (Ms i).frame.world) /\
          {i | i IN J /\ x i = y i} IN U} /\ {i | i IN J /\ satis (Ms i) (r i) phi} IN U` by metis_tac[satis_in_world] >> fs[] >> `{i | i IN J /\ satis (Ms i) (r i) phi} ∩ {i | i IN J /\ x i = r i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ satis (Ms i) (r i) phi} INTER {i | i IN J /\ x i = r i} ⊆ {i | i IN J /\ satis (Ms i) (x i) phi}` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} ⊆ J` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ g i = x i} = {i | i IN J /\ x i = g i}` by rw[EXTENSION,EQ_IMP_THM] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	  `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} ⊆ {i | i IN J /\ satis (Ms i) (g i) phi}` by fs[SUBSET_DEF] >>
	  `{i | i IN J /\ satis (Ms i) (g i) phi} ⊆ J` by fs[SUBSET_DEF] >>
	  metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} =
     {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi}`
       by rw[EXTENSION,EQ_IMP_THM] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} ⊆
     {i | i IN J /\ x' i IN (Ms i).frame.world /\
     ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
       by (rw[SUBSET_DEF] >> qexists_tac `g x''` >> rw[]) >>
     `{i | i IN J /\ x' i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆ J` by fs[SUBSET_DEF] >>
      metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-------------------------------half 2---------------------------------------------------*)
>- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
        by metis_tac[EMPTY_NOTIN_ultrafilter] >> fs[GSYM MEMBER_NOT_EMPTY] >>
     simp[PULL_EXISTS] >> rw[ultraproduct_rel] >>
     `?x g. (f IN fc /\
     ((!i. i IN J ==> g i IN (Ms i).frame.world) /\
     {i | i IN J /\ x i = g i} IN U) /\
     {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U) /\
     (!i. i IN J ==> (Ms i).frame.world <> {}) /\
     (!i. i IN J ==> x i IN (Ms i).frame.world) /\
     satis (ultraproduct_model U J Ms)
     {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U} phi`
     suffices_by (rw[] >> qexists_tac `x'` >> rw[] (* 2 *)
                 >- (map_every qexists_tac [`f`,`g`] >> rw[])
		 >- metis_tac[MEMBER_NOT_EMPTY]) >>
     map_every qexists_tac
     [`\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
	  else CHOICE (Ms i).frame.world`,
     `\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
	  else CHOICE (Ms i).frame.world`]>> rw[] (* 8 *)
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
	     metis_tac[MEMBER_NOT_EMPTY]) >>
	`CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
	fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
     >- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
         ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
	{i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)}`
	  by (rw[SUBSET_DEF] >>
	     `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
	       by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
	             by fs[] >>
		  metis_tac[MEMBER_NOT_EMPTY]) >>
             `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
	     {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
	       by metis_tac[CHOICE_DEF] >> fs[]) >>
	`{i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)} ⊆ J` by fs[SUBSET_DEF] >>
	metis_tac[ultrafilter_def,proper_filter_def,filter_def]) 
     >- metis_tac[ultraproduct_world]
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
	     metis_tac[MEMBER_NOT_EMPTY]) >>
	`CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
	fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- (`{i | i IN J /\
        satis (Ms i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world) phi} IN U`
	  by (`{i | i IN J /\ f i IN (Ms i).frame.world /\
             ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
	     {i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi}`
	       by (rw[SUBSET_DEF] >>
	          `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
		    by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
		          by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
		  `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
		  {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
		    by metis_tac[CHOICE_DEF] >> fs[]) >>
             `{i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi} ⊆ J` by fs[SUBSET_DEF] >>
	     metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
        `{y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} IN (ultraproduct_model U J Ms).frame.world`
	  by
	  (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
	  `?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} =
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
	  suffices_by metis_tac[ultraproduct_world] >>
	  qexists_tac
	  `\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)` >> rw[] (* 2 *)
	  >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
	       by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	             by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
	     `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	     {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	       by metis_tac[CHOICE_DEF] >> fs[])
	  >- metis_tac[CHOICE_DEF]) >>
	`(\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)) IN
	{y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U}`     
	  by (rw[] (* 2 *)
	     >- (Cases_on `?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi` (* 2 *)
	        >- (rw[] >>
		   `{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
	             by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	                   by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
		   `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
	           {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
	             by metis_tac[CHOICE_DEF] >> fs[])
		>- (rw[] >> metis_tac[CHOICE_DEF,ultraproduct_world]))
	     >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >> metis_tac[]))));



val prop_2_71 = store_thm(
  "prop_2_71",
  ``!U J Ms. (!i. i IN J ==> (Ms i) = M) /\ ultrafilter U J ==>
         !phi w. satis (ultraproduct_model U J Ms) {fw | Uequiv U J (models2worlds Ms) (\i.w) fw} phi <=> satis M w phi``,
  rw[EQ_IMP_THM] (* 2 *)
  >- (`!phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by metis_tac[satis_in_world] >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} <> {}`
       by metis_tac[EMPTY_NOTIN_ultrafilter] >>
     fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
  >- (` !phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by (`w IN M.frame.world` by metis_tac[satis_in_world] >>
          metis_tac[ultraproduct_world_constant]) >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       suffices_by metis_tac[] >>
     qexists_tac `\i.w` >> rw[] (* 2 *)
     >- (fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        `w IN M.frame.world` by metis_tac[satis_in_world] >>
	metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY])
     >- (`{i | i IN J /\ satis (Ms i) w phi} = J`
          suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	rw[EXTENSION,EQ_IMP_THM])));



val _ = Datatype`
        folmodel = <| domain : 'a set ;
	              consts : num |-> 'a;
	              fnsyms : num -> 'a list -> 'a;
		      predsyms : 'p -> 'a -> bool;
		      relsyms : 'r -> 'a -> 'a -> bool;
		      |>`;

val mm2folm_def = Define`
  mm2folm M = <| domain := M.frame.world ;
                 consts := FEMPTY;
                 fnsyms := \x y. ARB;
		 predsyms := \p w. (w IN M.frame.world /\ M.valt p w);
		 relsyms := \ (u:unit) w1 w2. (M.frame.rel w1 w2 /\ w1 IN M.frame.world /\ w2 IN M.frame.world) |>`;

val folmodels2domains_def = Define`
 folmodels2domains Ms = (\i. (Ms i).domain)`;



val ultraproduct_folmodel_def = Define`
  ultraproduct_folmodel U J Ms =
              <| domain := ultraproduct U J (folmodels2domains Ms);
                 consts := FUN_FMAP (\n. {fw | Uequiv U J (folmodels2domains Ms) (\i. ((Ms i).consts ' n)) fw}) (BIGINTER {FDOM (Ms i).consts | i IN J});
                 fnsyms := \n l. {fw | Uequiv U J (folmodels2domains Ms) (\i. ((Ms i).fnsyms n (MAP (\l0. l0 i) (MAP CHOICE l)))) fw} ;
		 predsyms := \p fu. ?f. f IN fu /\ {i | i IN J /\ f i IN (Ms i).predsyms p} IN U;
		 relsyms := \ (u:unit) fu gu.
		            ?f g. f IN fu /\ g IN gu /\ {i | i IN J /\ (Ms i).relsyms u (f i) (g i)} IN U |>`




val ultraproduct_world = store_thm(
  "ultraproduct_world",
  ``!U J MS.
    ultrafilter U J ==>
       (!v.
           v ∈ (ultraproduct_model U J MS).frame.world <=>
               (!i. i IN J ==> (MS i).frame.world <> {}) /\
               (∃x.
                   (∀i. i ∈ J ⇒ x i ∈ (MS i).frame.world) /\
                   v = {y | (∀i. i ∈ J ⇒ y i ∈ (MS i).frame.world) /\ {i | i ∈ J ∧ x i = y i} ∈ U}))``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >> qexists_tac `x` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]);


val ultraproduct_fol_world = store_thm(
  "ultraproduct_fol_world",
  ``!U J Ms.
    ultrafilter U J ==>
      (!v. v IN (ultraproduct_folmodel U J Ms).domain <=>
           (!i. i IN J ==> (Ms i).domain <> {}) /\
	   (?x.
               (!i. i IN J ==> x i IN (Ms i).domain) /\
	       v = {y | (!i. i IN J ==> y i IN (Ms i).domain) /\ {i | i IN J /\ x i = y i} IN U}))``,
  rw[ultraproduct_def,ultraproduct_folmodel_def, folmodels2domains_def,partition_def,Uequiv_def,Cart_prod_def] >>
  rw[EQ_IMP_THM]
  >- metis_tac[MEMBER_NOT_EMPTY]
  >> qexists_tac `x` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]);



  
val ultraproduct_fol_rel = save_thm(
  "ultraproduct_fol_rel",
  ``(ultraproduct_folmodel U J Ms).relsyms u w v``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_folmodel_def, folmodels2domains_def,partition_def,Uequiv_def,Cart_prod_def])

val ultraproduct_valt = save_thm(
  "ultraproduct_valt",
  ``v IN (ultraproduct_model U J MS).valt p``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])




val ultraproduct_folmodel_rel_gen = store_thm(
  "ultraproduct_folmodel_rel_gen",
  ``!U J Ms. ultrafilter U J ==>
      !fu gu. fu IN (ultraproduct_folmodel U J Ms).domain /\ gu IN (ultraproduct_folmodel U J Ms).domain ==>
        !rf rg. rf IN fu /\ rg IN gu /\ {i | i IN J /\ (Ms i).relsyms u (rf i) (rg i)} IN U ==>
	  (!f g. f IN fu /\ g IN gu ==> {i | i IN J /\ (Ms i).relsyms u (f i) (g i)} IN U)``,
  rw[] >> rfs[ultraproduct_fol_world] >>
  `f IN {y | (!i. i IN J ==> y i IN (Ms i).domain) /\ {i | i IN J /\ x' i = y i} IN U} /\
  g IN {y | (!i. i IN J ==> y i IN (Ms i).domain) /\ {i | i IN J /\ x i = y i} IN U}`
    by metis_tac[] >> fs[] >>
  `rf IN {y | (!i. i IN J ==> y i IN (Ms i).domain) /\ {i | i IN J /\ x' i = y i} IN U} /\
  rg IN {y | (!i. i IN J ==> y i IN (Ms i).domain) /\ {i | i IN J /\ x i = y i} IN U}`
    by metis_tac[] >> fs[] >>
  `{i | i IN J /\ x' i = rf i} ∩ {i | i IN J /\ x' i = f i} IN U`
    by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  `{i | i IN J /\ x i = g i} ∩ {i | i IN J /\ x i = rg i} IN U`
    by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  `({i | i IN J /\ x' i = rf i} ∩ {i | i IN J /\ x' i = f i}) ∩
  ({i | i IN J /\ x i = g i} ∩ {i | i IN J /\ x i = rg i}) IN U`
    by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  `(({i | i IN J /\ x' i = rf i} ∩ {i | i IN J /\ x' i = f i}) ∩
  ({i | i IN J /\ x i = g i} ∩ {i | i IN J /\ x i = rg i})) ∩ {i | i IN J /\ (Ms i).relsyms () (rf i) (rg i)} IN U`
    by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  `{i | i IN J /\ (Ms i).relsyms () (f i) (g i)} ⊆ J` by fs[SUBSET_DEF] >>
  `(({i | i IN J /\ x' i = rf i} ∩ {i | i IN J /\ x' i = f i}) ∩
  ({i | i IN J /\ x i = g i} ∩ {i | i IN J /\ x i = rg i})) ∩ {i | i IN J /\ (Ms i).relsyms () (rf i) (rg i)}
  ⊆ {i | i IN J /\ (Ms i).relsyms () (f i) (g i)}`
    suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  rw[INTER_DEF,SUBSET_DEF] >> metis_tac[]);






val thm_A_19 = store_thm(
  "thm_A_19",
  ``!U J Ms. ultrafilter U J ==>
      !phi σ σs. IMAGE σ univ(:num) SUBSET (ultraproduct_folmodel U J Ms).domain /\
                 (!i. i IN J ==> IMAGE (σs i) univ(:num) SUBSET (Ms i).domain) /\
		 (!a. a IN freevars phi ==> (!i. i IN J ==> ?fu. fu IN (σ a) /\ (σs i) a = fu i))==>
		   (fsatis (ultraproduct_folmodel U J Ms) σ phi <=>
		   {i | i IN J /\ fsatis (Ms i) (σs i) phi} IN U)``,
strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` >> rw[] (* 6 *)
(*-------------------- Rel case ----------------------*)
>- rw[EQ_IMP_THM,fsatis_def] (* 2 *)
   >- Cases_on `f` >> Cases_on `f0`
      >- `{i | i IN J /\ IMAGE (σs i) univ(:num) SUBSET (Ms i).domain /\
               feval (Ms i) (σs i) (fRrel () (fVar n) (fVar n'))} =
	  {i | i IN J /\ feval (Ms i) (σs i) (fRrel () (fVar n) (fVar n'))} `
	   by rw[EXTENSION,EQ_IMP_THM] >>
	 `{i | i IN J /\ feval (Ms i) (σs i) (fRrel () (fVar n) (fVar n'))} IN U` suffices_by metis_tac[] >>
	 fs[feval_def,interpret_def] >>
	 fs[ultraproduct_fol_rel] >>
	 `(σ n) IN (ultraproduct_folmodel U J Ms).domain /\ (σ n') IN (ultraproduct_folmodel U J Ms).domain`
	   by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
	 drule ultraproduct_folmodel_rel_gen >> rw[] >>
	 `!f0 g0. f0 IN (σ n) /\ g0 IN (σ n') ==> {i | i IN J /\ (Ms i).relsyms u (f0 i) (g0 i)} IN U`
	   by metis_tac[]
		   




``mm2folm (ultraproduct_model U J Ms) = ultraproduct_folmodel U J (\i. mm2folm (Ms i))``,


val Los_one_free_var_thm = store_thm(
  "Los_one_free_var_thm",
``!U J Ms.
ultrafilter U J ==>
  !phi σ σs. FINITE (freevars phi) ==>
             IMAGE σ univ(:num) SUBSET (ultraproduct_folmodel U J Ms).domain) /\
	     (!i. i IN J ==> IMAGE (σs i) univ(:num) SUBSET (Ms i).domain) ==>
	       (!fc. fc IN (ultraproduct_folmodel U J Ms).domain ==>
	         (fsatis (ultraproduct_folmodel U J Ms) σ phi <=>
		 (!x. x IN (freevars phi) ==> (!i. i IN J ==> (σ x) IN (σs i))) ==>
			          {i | i IN J /\ fsatis (Ms i) (σs i) phi} IN U))``,
strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` >> rw[] (* 6 *)
(* Var case *)
>- rw[EQ_IMP_THM,fsatis_def] (* 3 *)
   >- Cases_on `f`  (* 2 *)
      (* f  is a var *)
      >- Cases_on `f0`
         (* f0 is a var *) >- 
	 (fs[freevars_def,tvars_def] >> fs[feval_def,mm2folm_def,interpret_def]>> rfs[APPLY_UPDATE_THM] >>
	 qmatch_abbrev_tac `ss IN U` >>
	 `ss ⊆ J` by fs[Abbr`ss`,SUBSET_DEF] >>
	 rfs[ultraproduct_world] >> fs[ultraproduct_rel] >> rfs[] >>
	 `({i | i IN J /\ x' i = f i} ∩ {i | i IN J /\ x' i = g i}) ∩ {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U`
	   by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	 `({i | i IN J /\ x' i = f i} ∩ {i | i IN J /\ x' i = g i}) ∩ {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} ⊆ ss`
	   suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
	 rw[SUBSET_DEF,Abbr`ss`] >> rfs[] >> qexists_tac `g` >> rw[] >> Cases_on `x''' = n` >> rw[APPLY_UPDATE_THM] >>
	 fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
	 (* f0 is const *)
	 fs[freevars_def,tvars_def] >> fs[feval_def,mm2folm_def,interpret_def]>> rfs[APPLY_UPDATE_THM] >>
	 qmatch_abbrev_tac `ss IN U` >>
	 `ss ⊆ J` by fs[Abbr`ss`,SUBSET_DEF] >>
	 rfs[ultraproduct_world] >> fs[ultraproduct_rel] >> rfs[] >>
	 





val countably_incomplete_def = Define`
  countably_incomplete U J <=> ultrafilter U J /\ (?SS. SS ⊆ U /\ BIGINTER SS = {})`;

Let L be a countable ﬁrst-order language, U a countably incomplete ultraﬁlter over a non-empty set I, and M an L-model. The ultrapowerQU M is countably saturated.

val agree_on_freevars_satis_lemma = store_thm(
  "agree_on_freevars_satis_lemma",
  ``!phi M σ. fsatis M σ phi ==> !σ'. IMAGE σ' univ(:num) ⊆ M.domain ==> (!x. x IN freevars phi ==> σ x = σ' x) ==> fsatis M σ' phi``,
  Induct_on `phi` >> rw[] (* 6 *)
  >- (Cases_on `f` >> Cases_on `f0` >> fs[freevars_def,tvars_def,SUBSET_DEF,fsatis_def,interpret_def,feval_def] >> rw[] >> rfs[])
  >- (Cases_on `f` >> fs[freevars_def,tvars_def,SUBSET_DEF,fsatis_def,interpret_def,feval_def] >> rw[] >> rfs[])
  >- (fs[fsatis_def,feval_def,freevars_def] (* 2 *) >> metis_tac[])
  >- (fs[fsatis_def,feval_def,freevars_def] (* 2 *) >> metis_tac[])
  >- (fs[fsatis_def,feval_def,freevars_def] >> qexists_tac `x` >> rw[] >>
     `!a. a IN freevars phi ==> ((n =+ x) σ) a = ((n =+ x) σ') a`
       by (rw[] >> Cases_on `a = n` >> rw[APPLY_UPDATE_THM]) >>
     `IMAGE ((n =+ x) σ) univ(:num) SUBSET M.domain /\
     IMAGE ((n =+ x) σ') univ(:num) SUBSET M.domain`
       by (fs[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x'' = n` >> fs[APPLY_UPDATE_THM] >> metis_tac[]) >>
     metis_tac[])
  >- (fs[fsatis_def,feval_def,freevars_def] >> Cases_on `f` >> Cases_on `f0` (* 4 *) >> fs[tvars_def,interpret_def]));


val 






val lemma_2_73_modal = store_thm(
  "lemma_2_73_modal",
  ``!U J Ms. countably_incomplete U J /\ (!i. i IN J ==> Ms i = M)
             ==> countably_saturated (mm2folm (ultraproduct_model U J Ms))``
  rw[countably_saturated_def,n_saturated_def,frealizes_def,consistent_def] >>
  `countable G` by cheat >>
  `?Is. (!n. n IN univ(:num) ==> (Is n) IN U) /\ (!n. Is (n + 1) ⊆ Is n) /\ BIGINTER {Is n | n IN univ(:num)} = {}` by cheat >>
  fs[COUNTABLE_ALT_BIJ] (* 2 *)
  >- (`G ⊆ G` by fs[SUBSET_DEF] >>
     `?σ. IMAGE σ univ(:num) SUBSET M'.domain /\ (!phi. phi IN G ==> fsatis M' σ phi)` by metis_tac[] >>
     qexists_tac `σ x` >> rw[] (* 2 *)
     >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
     >- (fs[fsatis_def] >>
        `feval M' σ phi` by metis_tac[] >> rw[] (* 2 *)
	>- (fs[IMAGE_DEF,SUBSET_DEF] >> rw[] >> Cases_on `x'' = x` >> fs[APPLY_UPDATE_THM] (* 2 *) >> metis_tac[])
	>- (`IMAGE σ univ(:num) SUBSET M'.domain` by metis_tac[] >>
	   `fsatis M' ((x =+ σ x) σ') phi` suffices_by metis_tac[fsatis_def] >>
           `fsatis M' σ phi` by metis_tac[fsatis_def] >>
           `IMAGE ((x =+ σ x) σ') univ(:num) SUBSET M'.domain /\
	   IMAGE σ univ(:num) SUBSET M'.domain /\
	   (!a. a IN freevars phi ==> σ a = ((x =+ σ x) σ') a)`
	     suffices_by metis_tac[agree_on_freevars_satis_lemma] >>
	   rw[IMAGE_DEF,SUBSET_DEF] (* 2 *)
	   >- (Cases_on `x'' = x` >> fs[APPLY_UPDATE_THM] (* 2 *)
	      >> (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
	   >- (fs[ftype_def] >>
	      `phi IN {phi | freevars phi SUBSET {x}}` by metis_tac[SUBSET_DEF] >>
	      fs[] >> `a IN {x}` by metis_tac[SUBSET_DEF] >> fs[APPLY_UPDATE_THM]))))
	      
	   
	   
	
  >- qabbrev_tac `Xs = \n. if n = 0 then Is 0
                        else (Is n) ∩ {i| i IN J /\ ?x0. !a σ. a <= n ==> fsatis (mm2folm (Ms i)) ((x =+ x0)σ) ((enumerate G) (a - 1))}` >>
     `!n. {i |
                 i IN J /\
                 ?x0.
                    !a σ.
                       a <= n ==>
                       fsatis (mm2folm (Ms i)) ((x =+ x0) σ)
                         (enumerate G (a - 1))} IN U`
       by rw[] >>
          `FINITE {(enumerate G) (a - 1) | a <= n'}`
	    by cheat >>
	  `?ff.!w M.
            w IN M.frame.world ==>
            (satis M w ff <=> !f. f IN {enumerate G (a - 1) | a <= n'} ==> satis M w f)` by metis_tac[BIGCONJ_EXISTS_2]
  



val thm_2_74_half1 = store_thm(
  "thm_2_74",
  ``!M N. ultrafilter U J /\ (!i. i IN J ==> (Ms i) = M) /\ (!i. i IN J ==> (Ns i) = N) ==>
	  bisim_world (ultraproduct_model U J Ms) (ultraproduct_model U J Ns)
          {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} {fw | Uequiv U J (models2worlds Ns) (\i. v) fw} ==>
	  (!phi. satis M w phi <=> satis N v phi)``,
  rw[] >> `modal_eq (ultraproduct_model U J Ms) (ultraproduct_model U J Ns)
                    {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} {fw | Uequiv U J (models2worlds Ns) (\i. v) fw}`
            by metis_tac[thm_2_20] >> fs[modal_eq_tau] >> metis_tac[prop_2_71]);


val exercise_2_5_4_lemma = store_thm(
  "exercise_2_5_4_lemma",
  ``proper_filter {ss | ss ⊆ univ(:num) /\ FINITE (univ(:num) DIFF ss)} univ(:num)``,
  rw[ultrafilter_def,proper_filter_def,filter_def] (* 5 *)
  >- rw[POW_DEF,SUBSET_DEF]
  >- (`(univ(:num) DIFF X) ∪ (univ(:num) DIFF Y) = (univ(:num) DIFF (X INTER Y))`
       by rw[EXTENSION,EQ_IMP_THM,DIFF_DEF,INTER_DEF] >>
     metis_tac[FINITE_UNION])
  >- (`(univ(:num) DIFF Z) ⊆ (univ(:num) DIFF X)` by (fs[SUBSET_DEF,DIFF_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_FINITE])
  >- (simp[EXTENSION,EQ_IMP_THM] >> qexists_tac `{}` >> rw[] >> fs[POW_DEF,SUBSET_DEF]));


val exercise_2_5_4 = store_thm(
  "exercise_2_5_4",
  ``?U. ultrafilter U univ(:num) /\ (!ss. ss IN U ==> INFINITE ss) /\
  {ss | ss ⊆ univ(:num) /\ FINITE (univ(:num) DIFF ss)} ⊆ U``,
  `proper_filter {ss | ss ⊆ univ(:num) /\ FINITE (univ(:num) DIFF ss)} univ(:num)`
    by metis_tac[exercise_2_5_4_lemma] >>
  `?U. ultrafilter U univ(:num) /\ {ss | ss ⊆ univ(:num) /\ FINITE (univ(:num) DIFF ss)} ⊆ U`
    by metis_tac[ultrafilter_theorem] >>
  qexists_tac `U` >> rw[] >>
  SPOSE_NOT_THEN ASSUME_TAC >>
  `ss ⊆ univ(:num)` by fs[SUBSET_DEF] >>
  `univ(:num) DIFF (univ(:num) DIFF ss) = ss` by metis_tac[DIFF_DIFF_SUBSET] >>
  `(univ(:num) DIFF ss) IN {ss | ss SUBSET univ(:num) /\ FINITE (univ(:num) DIFF ss)}` by fs[] >>
  `(univ(:num) DIFF ss) IN U` by fs[SUBSET_DEF] >>
  `(univ(:num) DIFF ss) ∩ ss IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
  `(univ(:num) DIFF ss) INTER ss = {}` by fs[EXTENSION,EQ_IMP_THM] >>
  metis_tac[EMPTY_NOTIN_ultrafilter]);


val example_2_72 = store_thm(
  "example_2_72",
  ``?U. countably_incomplete U univ(:num)``,
  `?U.
      ultrafilter U univ(:num) /\ (!ss. ss IN U ==> INFINITE ss) /\
      {ss | ss SUBSET univ(:num) /\ FINITE (univ(:num) DIFF ss)} SUBSET
      U` by metis_tac[exercise_2_5_4] >>
  qexists_tac `U` >> rw[countably_incomplete_def] >>
  qexists_tac `{ss | ?x. ss = univ(:num) DIFF {x}}` >> rw[] (* 2 *)
  >- (`{ss | ?x. ss = univ(:num) DIFF {x}} ⊆ {ss | ss SUBSET univ(:num) /\ FINITE (univ(:num) DIFF ss)}`
       suffices_by fs[SUBSET_DEF] >>
     rw[SUBSET_DEF] >>
     `{x'} ⊆ univ(:num)` by fs[] >>
     `(univ(:num) DIFF (univ(:num) DIFF {x'})) = {x'}` by metis_tac[DIFF_DIFF_SUBSET] >>
     fs[])
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
     fs[GSYM MEMBER_NOT_EMPTY] >>
     `?P. (?x. P = univ(:num) DIFF {x}) /\ x NOTIN P` suffices_by metis_tac[] >>
     qexists_tac `univ(:num) DIFF {x}` >> rw[] >> qexists_tac `x` >> rw[]));
  
  

val thm_2_74_half2 = store_thm(
  "thm_2_74_half2",
  ``!M N w v. (w IN M.frame.world /\ v IN N.frame.world /\ 
          (!phi. satis M w phi <=> satis N v phi)) ==>
          (?U J:num -> bool. ultrafilter U J /\ (!i. i IN J ==> (Ms i) = M) /\ (!i. i IN J ==> (Ns i) = N) ==>
	  bisim_world (ultraproduct_model U J Ms) (ultraproduct_model U J Ns)
          {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} {fw | Uequiv U J (models2worlds Ns) (\i. v) fw})``,
  rw[] >> `?U. countably_incomplete U univ(:num)` by metis_tac[example_2_72] >>
  map_every qexists_tac [`U`,`univ(:num)`] >> rw[] >>
  `countably_saturated (mm2folm (ultraproduct_model U univ(:num) Ms)) /\
  countably_saturated (mm2folm (ultraproduct_model U univ(:num) Ns))` by metis_tac[lemma_2_73_modal] >>
  irule thm_2_65_corollary (* 5 *)
  >- fs[]
  >- fs[]
  >- (rw[ultraproduct_world] (* 2 *)
     >- metis_tac[MEMBER_NOT_EMPTY]
     >- (qexists_tac `\i.w` >> rw[EXTENSION,EQ_IMP_THM] (* 3 *)
        >- (fs[Uequiv_def,Cart_prod_def,models2worlds_def] >> metis_tac[])
	>- fs[Uequiv_def,Cart_prod_def,models2worlds_def]
	>- (fs[Uequiv_def,Cart_prod_def,models2worlds_def] >> metis_tac[MEMBER_NOT_EMPTY])))
  >- (rw[ultraproduct_world] (* 2 *)
     >- metis_tac[MEMBER_NOT_EMPTY]
     >- (qexists_tac `\i.v` >> rw[EXTENSION,EQ_IMP_THM] (* 3 *)
        >- (fs[Uequiv_def,Cart_prod_def,models2worlds_def] >> metis_tac[])
	>- fs[Uequiv_def,Cart_prod_def,models2worlds_def]
	>- (fs[Uequiv_def,Cart_prod_def,models2worlds_def] >> metis_tac[MEMBER_NOT_EMPTY])))
  >- (fs[modal_eq_tau] >> rw[EQ_IMP_THM] (* 2 *)
     >> metis_tac[prop_2_71]));
     






val _ = export_theory();

