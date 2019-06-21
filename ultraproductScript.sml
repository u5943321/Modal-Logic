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





val folmodels2Doms_def = Define`
  folmodels2worlds FMS = \i. (FMS i).Dom`


 
val ultraproduct_folmodel_def = Define`
   ultraproduct_folmodel U I FMS = 
    <| Dom := ultraproduct U I (folmodels2Doms FMS) ;
       Fun := \n fs fc. (\i. ((FMS i).Fun n (MAP ((\f. f i) o CHOICE) fs))) IN fc;
       Pred := \p zs. ({i IN I | (FMS i).Pred p (MAP ((\f. f i) zs) o CHOICE) zs} IN U) |>`;


Theorem lemma_2_73:
  !U I MS M. 
         countably_incomplete U I /\
         (!i. i IN I ==> MS i = M) ==> 
             countably_saturated (mm2folm (ultraproduct_model U I M))
Proof
  rw[countably_saturated_def,n_saturated_def] >>
  `countable G` by cheat >> fs[countable_def]
  `?In. (!n: num. In (n+1) ⊆ In n) /\ BIGINTER {(In n)| n IN (univ (:num))} = {}` by cheat >>
  qabbrev_tac 
   `X = \n. if n = 0 then In 0 
            else (In n) ∩ {i IN I | (?σ. !m. m < n ==> fsatis (MS i) σ (f' m))}`

QED


Theorem Los_Thm :
  !D I. ultrafilter D I ==> 
        !phi. 
             (feval σ (ultraproduct_model U I MS) phi) <=> 
             {i IN I | feval (\n. σ n i) (MS i) phi} IN U
Proof


QED





val _ = export_theory();

