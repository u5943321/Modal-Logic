open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory; 

open nlistTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_1";

val DU_def = Define`
DU (f, dom) = <| frame := <| world := {n | (nfst n) IN dom /\ (nsnd n) IN (f (nfst n)).frame.world };
rel := λn1 n2. nfst n1 = nfst n2 /\ nfst n1 IN dom /\ (f (nfst n1)).frame.rel (nsnd n1) (nsnd n2) |>;
          valt := λv n. nfst n IN dom /\ (f (nfst n)).valt v (nsnd n) |>`;



val M_union_def = Define` 
M_union (M1:'a model) (M2:'a model) = DU ((λn. if n = 0 then M1 else M2), {x | x = 0 \/ x = 1})`;



val prop_2_3 = store_thm(
"prop_2_3",
``!n f. (nfst n) IN dom ==> (satis (f (nfst n)) (nsnd n) phi <=> satis (DU (f, dom)) n phi)``,
Induct_on `phi` >> rw[satis_def]
>- (rw[satis_def,DU_def] >> metis_tac[IN_DEF])
>- (eq_tac
   >- (rpt strip_tac
   >> fs[DU_def])
   >- (rpt strip_tac
   >> fs[DU_def]))
>- (eq_tac
>- (rpt strip_tac
   >- fs[DU_def]
   >- (qexists_tac `npair (nfst n) v`
   >> `nfst (npair (nfst n) v) = nfst n` by metis_tac[nfst_npair]
   >> `nfst (npair (nfst n) v) IN dom` by fs[]
   >> `nsnd (npair (nfst n) v) = v` by metis_tac[nsnd_npair]
   >> `satis (f (nfst (npair (nfst n) v))) (nsnd (npair (nfst n) v)) phi ⇔ satis (DU (f,dom)) (npair (nfst n) v) phi` by fs[]
   >> `(satis (f (nfst n)) v phi ⇔ satis (DU (f,dom)) (nfst n ⊗ v) phi)` by fs[]
   >> `satis (DU (f,dom)) (nfst n ⊗ v) phi` by metis_tac[]
   >> `(f (nfst n)).frame.rel (nsnd n) (nsnd (nfst n ⊗ v))` by fs[IN_DEF,DU_def]
   >> `nfst n ⊗ v ∈ (DU (f,dom)).frame.rel n` by fs[IN_DEF,DU_def]
   >> fs[]
   >> fs[DU_def,nfst_npair,nsnd_npair]))
>- (rpt strip_tac
   >- fs[DU_def]
   >- (qexists_tac `nsnd v`
   >> `nfst v = nfst n` by fs[IN_DEF,DU_def]
   >> `nfst v IN dom` by fs[]
   >> `(satis (f (nfst v)) (nsnd v) phi ⇔ satis (DU (f,dom)) v phi)` by metis_tac[]
   >> `satis (f (nfst v)) (nsnd v) phi` by fs[]
   >> `satis (f (nfst n)) (nsnd v) phi` by metis_tac[]
   >> `nsnd v ∈ (f (nfst n)).frame.rel (nsnd n)` by fs[IN_DEF,DU_def]
   >> fs[]
   >> fs[DU_def])))
   );



val SUBMODEL_def = Define`
!M1 M2. SUBMODEL M1 M2 <=> (M1.frame.world) ⊆ (M2.frame.world) /\
                         (!w1. w1 IN M1.frame.world ==>
                         (!v. M1.valt v w1 <=> M2.valt v w1) /\
                         (!w2. w2 IN M1.frame.world ==> (M1.frame.rel w1 w2 <=> M2.frame.rel w1 w2)))`;
                         


val GENSUBMODEL_def = Define`
!M1 M2. GENSUBMODEL M1 M2 <=> SUBMODEL M1 M2 /\
                     (!w1. w1 IN M1.frame.world ==>
                     (!w2. w2 IN M2.frame.world /\ M2.frame.rel w1 w2 ==> w2 IN M1.frame.world))`;



val prop_2_6 = store_thm(
"prop_2_6",
``!n phi M1 M2. GENSUBMODEL M1 M2 /\ n IN M1.frame.world ==> (satis M1 n phi <=> satis M2 n phi)``,
Induct_on `phi` >> rw[satis_def]
>- (eq_tac
   >- (rpt strip_tac
      >- fs[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
      >- (fs[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
          >> `∀v. M1.valt v n ⇔ M2.valt v n` by metis_tac[]
          >> metis_tac[IN_DEF]))
   >- (rpt strip_tac
      >> fs[SUBMODEL_def,GENSUBMODEL_def,SUBSET_DEF]
      >> `∀v. M1.valt v n ⇔ M2.valt v n` by metis_tac[]
      >> metis_tac[IN_DEF]))
>- (eq_tac
   >- (rpt strip_tac
      >- (`satis M1 n phi ⇔ satis M2 n phi` by metis_tac[]
         >> metis_tac[])
      >- (`satis M1 n phi' ⇔ satis M2 n phi'` by metis_tac[]
         >> metis_tac[]))
   >- (rpt strip_tac
      >- (`satis M1 n phi ⇔ satis M2 n phi` by metis_tac[]
         >> metis_tac[])
      >- (`satis M1 n phi' ⇔ satis M2 n phi'` by metis_tac[]
         >> metis_tac[])))
>- (eq_tac
   >- (rpt strip_tac
      >> metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def])
   >- (rpt strip_tac
      >> metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]))
>- (eq_tac
   >- (rpt strip_tac
      >- metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
      >- (qexists_tac `v`
         >> rpt strip_tac
         >- metis_tac[SUBMODEL_def,GENSUBMODEL_def,IN_DEF]
         >- metis_tac[SUBMODEL_def,GENSUBMODEL_def,SUBSET_DEF]
         >- metis_tac[]))
   >- (rpt strip_tac
      >> qexists_tac `v`
      >> metis_tac[SUBMODEL_def,GENSUBMODEL_def,IN_DEF]))
);


      
val hom_def = Define`
hom f M1 M2 <=> (!w. w IN M1.frame.world ==> ((f w) IN M2.frame.world /\ (!p. w IN M1.valt p ==> (f w) IN M2.valt p) /\
                                            (!u. u IN M1.frame.world ==> (M1.frame.rel w u ==> M2.frame.rel (f w) (f u)))))`;



val strong_hom_def = Define`
strong_hom f M1 M2 <=> (!w. w IN M1.frame.world ==> ((f w) IN M2.frame.world /\ (!p. w IN M1.valt p <=> (f w) IN M2.valt p) /\
                                            (!u. u IN M1.frame.world ==> (M1.frame.rel w u <=> M2.frame.rel (f w) (f u)))))`;



val embedding_def = Define`
embedding f M1 M2 <=> (strong_hom f M1 M2 /\ INJ f M1.frame.world M2.frame.world)`;



val iso_def = Define`
iso f M1 M2 <=> (strong_hom f M1 M2 /\ BIJ f M1.frame.world M2.frame.world)`;



val tau_theory_def = Define`
!M w. tau_theory M w  = {form | satis M w form}`;



val modal_eq_def = Define`
!M M' w w'. modal_eq M M' w w'<=> (tau_theory M w = tau_theory M' w')`;



val tau_theory_model_def = Define`
!M. tau_theory_model M = {form | !w. w IN M.frame.world ==> satis M w form}`;



val modal_eq_model_def = Define`
!M M'. modal_eq_model M M' <=> (tau_theory_model M = tau_theory_model M')`;



val lemma_2_9 = store_thm(
"lemma_2_9",
``!M M' w w' f form. strong_hom f M M' /\ (f w) = w' /\ w IN M.frame.world /\ SURJ f M.frame.world M'.frame.world ==> (satis M w form <=> satis M' w' form) ``,
Induct_on `form` >> rw[satis_def]
>- metis_tac[strong_hom_def]
>- metis_tac[strong_hom_def]
>- metis_tac[strong_hom_def]
>- (eq_tac
   >- (rpt strip_tac
      >- metis_tac[strong_hom_def]
      >- (qexists_tac `f v`
         >> metis_tac[strong_hom_def,IN_DEF]))
   >- (rpt strip_tac
      >> `?x. x IN M.frame.world /\ f x = v` by metis_tac[SURJ_DEF]
      >> qexists_tac `x`
      >> metis_tac[strong_hom_def,IN_DEF])
     ));
      
      

val prop_2_9 = store_thm(
"prop_2_9",
``!M M' w w' f form. strong_hom f M M' /\ (f w) = w' /\ w IN M.frame.world /\ SURJ f M.frame.world M'.frame.world ==> modal_eq M M' w w' ``,
rw[modal_eq_def,tau_theory_def]
>> `!form. satis M w form <=> satis M' (f w) form` suffices_by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
>> metis_tac[lemma_2_9]);



val prop_2_9_ii = store_thm(
"prop_2_9_ii",
``!M M' f. iso f M M' ==> modal_eq_model M M'``,
fs[modal_eq_model_def,iso_def,tau_theory_model_def]
>> rpt strip_tac
>> `!form. (∀w. w ∈ M.frame.world ⇒ satis M w form) <=>  (∀w. w ∈ M'.frame.world ⇒ satis M' w form)` suffices_by fs[SET_EQ_SUBSET,SUBSET_DEF]
>> fs[BIJ_DEF]
>> rpt strip_tac
>> eq_tac
   >- (rpt strip_tac
   >> `?v. v IN M.frame.world /\ f v = w` by metis_tac[SURJ_DEF]
   >> `satis M v form` by metis_tac[]
   >> `satis M' (f v) form` by metis_tac[lemma_2_9]
   >> rw[])
   >- (rpt strip_tac
   >> `(f w) IN M'.frame.world` by metis_tac[strong_hom_def]
   >> `satis M' (f w) form` by metis_tac[]
   >> metis_tac[lemma_2_9])
);



val bounded_mor_def = Define`
!M M' f. bounded_mor f M M' <=> (!w. w IN M.frame.world ==>
((f w) IN M'.frame.world) /\
(!a. (satis M w (VAR a) <=> satis M' (f w) (VAR a))) /\
(!v. v IN M.frame.world /\ M.frame.rel w v ==> M'.frame.rel (f w) (f v)) /\
(!v'. v' IN M'.frame.world /\ M'.frame.rel (f w) v' ==> ?v. v IN M.frame.world /\ M.frame.rel w v /\ f v = v'))`;



val bounded_mor_image_def = Define`
!f M M. bounded_mor_image f M M' = (bounded_mor f M M' /\ (SURJ f M.frame.world M'.frame.world))`;



val prop_2_14 = store_thm(
"prop_2_14",
``!M M' w f form. bounded_mor f M M' /\ w IN M.frame.world ==> (satis M w form <=> satis M' (f w) form)``,
Induct_on `form` >> rw[satis_def]
>- (eq_tac
   >- (rpt strip_tac
     >- metis_tac[bounded_mor_def]
     >- (`(!a. (satis M w (VAR a) <=> satis M' (f w) (VAR a)))` by metis_tac[bounded_mor_def]
   >> fs[satis_def]
   >> metis_tac[]))
   >- (rpt strip_tac
   >> fs[bounded_mor_def,satis_def,IN_DEF]))
>- (eq_tac
  >- (rpt strip_tac
    >- (`satis M w form ⇔ satis M' (f w) form` by metis_tac[]
       >> fs[])
    >- (`satis M w form' ⇔ satis M' (f w) form'` by metis_tac[]
       >> fs[]))
  >- (rpt strip_tac
    >- (`satis M w form ⇔ satis M' (f w) form` by metis_tac[]
       >> fs[])
    >- (`satis M w form' ⇔ satis M' (f w) form'` by metis_tac[]
       >> fs[])))
>- fs[bounded_mor_def,IN_DEF,satis_def]
>- (eq_tac
  >- (rpt strip_tac
     >- metis_tac[bounded_mor_def]
     >- (qexists_tac `f v`
       >> (rpt strip_tac
       >- metis_tac[bounded_mor_def,IN_DEF]
       >- metis_tac[bounded_mor_def]
       >- metis_tac[])))
  >- (rpt strip_tac
  >> `?x. x IN M.frame.world /\ M.frame.rel w x /\ f x = v` by metis_tac[bounded_mor_def,IN_DEF]
  >> qexists_tac `x`
  >> rpt strip_tac
    >- metis_tac[IN_DEF]
    >- metis_tac[]
    >- metis_tac[]))
);



(* tree-like lemma *)

(* no-loop lemma *)
val RESTRICT_def = Define`
RESTRICT R s x y <=> R x y /\ x IN s /\ y IN s`;



val tree_def = Define`
tree S r <=>
  r IN S.world /\ (!t. t IN S.world ==> RTC (RESTRICT S.rel S.world) r t) /\
  (!r0. r0 IN S.world ==> ¬S.rel r0 r) /\
  (∀t. t ∈ S.world ∧ t ≠ r ==> ∃!t0. t0 ∈ S.world ∧ S.rel t0 t)`;



val RTC_PREDECESSOR_LEMMA = store_thm(
"RTC_PREDECESSOR_LEMMA",
``!R x y. RTC R x y ==> x <> y ==> ?p. R p y /\ p <> y``,
gen_tac >>
ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >>
rw[] >> metis_tac[]);



val TC_PREDECESSOR_LEMMA = store_thm(
"TC_PREDECESSOR_LEMMA",
``!R x y. TC R x y ==> x <> y ==> ?p. R p y /\ p <> y``,
gen_tac >>
ho_match_mp_tac relationTheory.TC_STRONG_INDUCT_LEFT1 >>
rw[] >> metis_tac[]);



val _ = clear_overloads_on "R";
val tree_no_loop = store_thm(
"tree_no_loop",
``!s r. tree s r ==> !t0 t. (TC (RESTRICT s.rel s.world) t0 t) ==> t0 <> t``,
rpt gen_tac >> strip_tac >>
qabbrev_tac `R = RESTRICT s.rel s.world` >>
rpt strip_tac >>
`R^* r t` by
(`?t'. R t0 t' /\ R^+ t' t` by metis_tac[TC_CASES1] >> fs[Abbr`R`,RESTRICT_def] >> metis_tac[tree_def]) >>
`!t1 t2. R^* t1 t2 ==> (t1 = r) ==> ¬R^+ t2 t2` suffices_by metis_tac[] >>
ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT_RIGHT1 >>
rpt strip_tac >-
(rw[] >> metis_tac[TC_CASES2,tree_def,RESTRICT_def]
)
>-
(rw[] >>
rename[`R^* r t0`,`¬R^+ t0 t0`,`R t0 t`] >>
`?t1. R t1 t /\ R^* t t1` by metis_tac[TC_CASES2,TC_RTC,RTC_REFL] >>
Cases_on `t0 = t1` >-
(metis_tac[EXTEND_RTC_TC_EQN])
>- (`t <> r` by metis_tac[tree_def,RESTRICT_def]
>> `t0 IN s.world /\ t1 IN s.world` by metis_tac[RESTRICT_def]
>> `s.rel t0 t /\ s.rel t1 t` by metis_tac[RESTRICT_def]
>> metis_tac[tree_def,RESTRICT_def]
)
)
);




(* tree-like model lemma *)
                                


val rooted_model_def = Define`
!M x M'. rooted_model M x M' <=> x IN M'.frame.world /\
                                 (!a. a IN M.frame.world <=> (a IN M'.frame.world /\ (RTC (RESTRICT M'.frame.rel M'.frame.world)) x a)) /\
                                 (!n1 n2. n1 IN M.frame.world /\ n2 IN M.frame.world ==>
				   (M.frame.rel n1 n2 <=> (RESTRICT M'.frame.rel M'.frame.world) n1 n2)) /\
                                 (!v n. M.valt v n <=> M'.valt v n)`;



val tree_like_model_def = Define`
!M. tree_like_model M <=> ?x. tree M.frame x`;


  
val bounded_preimage_rooted_def = Define`
bounded_preimage_rooted M x =
<| frame := <| world := {n| nhd n = x /\
                            (LENGTH (listOfN n) > 0) /\
                            (!m. m < LENGTH (listOfN n) - 1 ==> (RESTRICT M.frame.rel M.frame.world) (nel m n) (nel (m + 1) n))};
               rel := λn1 n2. (LENGTH (listOfN n1) + 1 = LENGTH (listOfN n2)) /\
                              (RESTRICT M.frame.rel M.frame.world) (nlast n1) (nlast n2) /\
               (!m. m < LENGTH (listOfN n1) ==> (nel m n1) = (nel m n2)) |>;
   valt := λv n. M.valt v (nlast n) |>`;






val in_bounded_preimage_length_not_zero = store_thm(
"in_bounded_preimage_length_not_zero",
``!t0. t0 IN (bounded_preimage_rooted M x).frame.world ==> LENGTH (listOfN t0) <> 0``,
rpt strip_tac >> `LENGTH (listOfN t0) > 0` by fs[Once bounded_preimage_rooted_def,IN_DEF] >> `¬((LENGTH (listOfN t0)) > 0)` by rw[]);






val in_world_not_zero = store_thm(
"in_world_not_zero",
``!a. a IN (bounded_preimage_rooted M x).frame.world ==> a <> 0 ``,
simp[bounded_preimage_rooted_def]);




val in_world_LENGTH_1_ncons_x_0 = store_thm(
"in_world_LENGTH_1_ncons_x_0[simp]",
``(ncons x' 0) IN (bounded_preimage_rooted M x).frame.world <=> x' = x``,
rw[bounded_preimage_rooted_def]);






val empty_not_in_world = store_thm(
"empty_not_in_world",
``LENGTH (listOfN a) = 0 ==> ¬(a IN (bounded_preimage_rooted M x).frame.world)``,
rpt strip_tac >>
`LENGTH (listOfN a) > 0` by (fs[bounded_preimage_rooted_def] >> rw[] >> fs[]) >> simp[]);



val not_root_length_at_least_two = store_thm(
"not_root_length_at_least_two",
``(a IN (bounded_preimage_rooted M x).frame.world /\ a <> ncons x 0) ==> LENGTH (listOfN a) >= 2``,
rpt strip_tac
>> `¬(LENGTH (listOfN a) < 2)` suffices_by simp[]
>> SPOSE_NOT_THEN ASSUME_TAC
>> `LENGTH (listOfN a) = 0 \/ LENGTH (listOfN a) = 1` by metis_tac[DECIDE ``x < 2 <=> (x = 0 \/ x = 1)``]
  >- metis_tac[empty_not_in_world]
  >- (fs[ncons_x_0_LENGTH_1] >> metis_tac[in_world_LENGTH_1_ncons_x_0]));





val in_world_LENGTH_at_least_1 = store_thm(
"in_world_LENGTH_at_least_1",
``!l. l IN (bounded_preimage_rooted M x).frame.world ==> LENGTH (listOfN l) > 0``, simp[bounded_preimage_rooted_def]);

val len_nzero = SIMP_RULE (srw_ss()) [] LENGTH_nonzero |> CONJUNCT2

val napp_in_world = store_thm(
"napp_in_world",
``!l1 l2. (napp l1 l2) IN (bounded_preimage_rooted M x).frame.world /\ l1 <> 0 ==> l1 IN (bounded_preimage_rooted M x).frame.world``,
rw[bounded_preimage_rooted_def]
>- simp[nhd_napp]
>- simp[len_nzero]
>- (`(nel m l1) = (nel m (napp l1 l2))` by simp[nel_napp]
  >> `(m + 1) < LENGTH (listOfN l1)` by simp[]
  >> `(nel (m + 1) l1) = (nel (m + 1) (napp l1 l2))` by metis_tac[nel_napp]
  >> `LENGTH (listOfN l1) - 1 <= LENGTH (listOfN (napp l1 l2)) - 1` by simp[LENGTH_le_napp] 
  >> `m < LENGTH (listOfN (napp l1 l2)) − 1` by simp[] >> fs[]));

val LENGTH_nfront' = SIMP_RULE (srw_ss()) [] LENGTH_nfront

val nfront_in_world = store_thm(
"nfront_in_world",
``(x ∈ M.frame.world /\
  t ∈ (bounded_preimage_rooted M x).frame.world /\
  t ≠ ncons x 0) ==>
nfront t ∈ (bounded_preimage_rooted M x).frame.world``,
rpt strip_tac
>> rw[bounded_preimage_rooted_def]
      (* definition of model expanded, gives 3 subgoals *)
      (* first subgoal: nhd (nfront t) = x *)
      >- (`nhd t = x` by fs[bounded_preimage_rooted_def]
        >> `ntl t <> 0 /\ t <> 0` suffices_by rw[nhd_nfront]
        >> SPOSE_NOT_THEN ASSUME_TAC
        >> `ntl t = 0 \/ t = 0` by metis_tac[]
          >- (fs[ntl_zero_empty_OR_ncons]
            >- metis_tac[in_world_not_zero]
            >- fs[in_world_LENGTH_1_ncons_x_0]
          )
          >- metis_tac[in_world_not_zero]
      )
      (* second subgoal: LENGTH of a non-root element > 0 *)
      >- (`LENGTH (listOfN t) ≥ 2` by metis_tac[not_root_length_at_least_two]
        >> `t <> 0` by metis_tac[in_world_not_zero] >> fs[] 
        >> `nlen (nfront t) + 1 >= 2` by simp[LENGTH_nfront']
        >> simp[])
      (* third subgoal: every adjacent element in nfront are linked *)
      >- (fs[nel_nfront]
        >> `t <> 0` by metis_tac[in_world_not_zero]
        >> `nlen (nfront t) + 1 = nlen t` by simp[LENGTH_nfront']
        >> `nlen (nfront t) <= nlen t` by simp[]
        >> `m < nlen t - 1` by simp[]
        >> fs[bounded_preimage_rooted_def]));

val not_root_length_at_least_two' =
  SIMP_RULE (srw_ss()) [] not_root_length_at_least_two
val nel_nfront' = SIMP_RULE (srw_ss()) [] nel_nfront

val nfront_rel = store_thm(
"nfront_rel",
``(x ∈ M.frame.world /\
  t ∈ (bounded_preimage_rooted M x).frame.world /\
  t ≠ ncons x 0) ==>
(bounded_preimage_rooted M x).frame.rel (nfront t) t``,
rpt strip_tac
>> rw[bounded_preimage_rooted_def]
  >- (`t <> 0` by metis_tac[in_world_not_zero]
       >> simp[LENGTH_nfront'])
  >- (`nlen t >= 2` by metis_tac[not_root_length_at_least_two']
    >> ONCE_REWRITE_TAC [nlast_nel]
    >> `t <> 0` by metis_tac[in_world_not_zero]
    >> `nlen (nfront t) + 1 = nlen t` by simp[LENGTH_nfront']
    >> `nlen (nfront t) = nlen t - 1` by simp[]
    >> rw[]
    >> `nlen t − 2 < nlen t − 1` by simp[]
    >> `nlen t − 2 < nlen (nfront t)` by simp[]
    >> simp[nel_nfront']
    >> `∀m.
         m < nlen t − 1 ⇒
         RESTRICT M.frame.rel M.frame.world (nel m t) (nel (m + 1) t)` by fs[bounded_preimage_rooted_def]
    >> `nlen t − 1 = nlen t − 2 + 1` by simp[]       
    >> metis_tac[])
  >- simp[nel_nfront']);


val nfront_in_world' = Q.store_thm(
  "nfront_in_world'",
  `x ∈ M.frame.world ∧ t ∈ (bounded_preimage_rooted M x).frame.world ∧
   1 < nlen t ==>
   nfront t ∈ (bounded_preimage_rooted M x).frame.world`,
  simp[bounded_preimage_rooted_def] >>
  qspec_then `t` STRUCT_CASES_TAC nsnoc_cases
  >- simp[] >>
  simp[nfront_napp_sing] >> rpt strip_tac
  >- (qspec_then `f` FULL_STRUCT_CASES_TAC nlist_cases >> fs[])
  >- (first_x_assum (qspec_then `m` mp_tac) >>
      simp[nel_napp]));

val prop_2_15_half1 = store_thm(
"prop_2_15_half1",
``!x M. x IN M.frame.world ==> tree (bounded_preimage_rooted M x).frame (nlist_of [x])``,
simp[tree_def] >> rpt strip_tac
>- (completeInduct_on `t`
    >> qspec_then `t` FULL_STRUCT_CASES_TAC nsnoc_cases
    >- simp[bounded_preimage_rooted_def]
    >> qspec_then `f` FULL_STRUCT_CASES_TAC nsnoc_cases
    >- simp[]
    >> rename[`napp (napp f0 (ncons l0 0)) (ncons l 0)`]
    >> strip_tac
    >> irule (RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2)
    >> qexists_tac `napp f0 (ncons l0 0)`
    >> qabbrev_tac `TreeM = bounded_preimage_rooted M x`
    >> conj_tac
    >- (simp[RESTRICT_def] >> reverse conj_tac
        >- (qabbrev_tac `pfx = napp f0 (ncons l0 0)` >>
            `nfront (napp pfx (ncons l 0)) = pfx` by simp[nfront_napp_sing] >>
            pop_assum (SUBST1_TAC o SYM) >> qunabbrev_tac `TreeM` >>
            irule nfront_in_world' >> simp[] >> simp[Abbr`pfx`]) >>
        simp[Abbr`TreeM`, bounded_preimage_rooted_def] >>
        simp[RESTRICT_def, nlast_napp, nel_napp] >>
        pop_assum mp_tac >>
        simp[bounded_preimage_rooted_def, RESTRICT_def, nel_napp] >>
        strip_tac >> first_assum (qspec_then `nlen f0` mp_tac) >>
        simp_tac (srw_ss()) [nel_napp2, nel_ncons_singl])
        >- (`(napp f0 (ncons l0 0)) < napp (napp f0 (ncons l0 0)) (ncons l 0)` by
  (simp[napp_nsnoc_le]) >>
  `nfront (napp (napp f0 (ncons l0 0)) (ncons l 0)) = (napp f0 (ncons l0 0))` by simp[nfront_napp_sing] >>
  `(napp (napp f0 (ncons l0 0)) (ncons l 0)) <> ncons x 0` by (SPOSE_NOT_THEN ASSUME_TAC >> `(napp f0 (ncons l0 0)) = 0` by metis_tac[napp_sing_eq] >>
  metis_tac[napp_ncons_not_nnil]) >> 
  `(napp f0 (ncons l0 0)) IN TreeM.frame.world` by metis_tac[nfront_in_world]
  >> metis_tac[]
  )
)
>- fs[bounded_preimage_rooted_def]
>- (simp[EXISTS_UNIQUE_DEF] >> rpt strip_tac
  >- (qexists_tac `nfront t` >> rpt strip_tac
    >- simp[nfront_in_world]
    >- simp[nfront_rel])
  >- (`∀m. m < LENGTH (listOfN x') ⇒ nel m x' = nel m t` by fs[bounded_preimage_rooted_def]
    >> `∀m. m < LENGTH (listOfN y) ⇒ nel m y = nel m t` by fs[bounded_preimage_rooted_def]
    >> `LENGTH (listOfN x') + 1 = LENGTH (listOfN t)` by fs[bounded_preimage_rooted_def]
    >> `LENGTH (listOfN y) + 1 = LENGTH (listOfN t)` by fs[bounded_preimage_rooted_def]
    >> `(LENGTH (listOfN x') + 1) - 1 = LENGTH (listOfN t) - 1` by fs[]
    >> `LENGTH (listOfN x') = LENGTH (listOfN t) - 1` by fs[]
    >> `(LENGTH (listOfN y) + 1) - 1 = LENGTH (listOfN t) - 1` by fs[]
    >> `LENGTH (listOfN y) = LENGTH (listOfN t) - 1` by fs[]
    >> `LENGTH (listOfN x') = LENGTH (listOfN y)` by fs[]
    >> `∀m. m < LENGTH (listOfN y) ⇒ nel m x' = nel m y` by metis_tac[]
    >> metis_tac[nel_eq_nlist]
)));



val root_in_rooted_model = store_thm(
"root_in_rooted_model",
``rooted_model M x M' ==> x IN M.frame.world``,
rpt strip_tac
>> `x IN M'.frame.world` by metis_tac[rooted_model_def]
>> `(RESTRICT M'.frame.rel M'.frame.world)^* x x` by metis_tac[RTC_REFL]
>> metis_tac[rooted_model_def]);



val nel_in_M_world = store_thm(
"nel_in_M_world",
``l IN (bounded_preimage_rooted M x).frame.world /\ rooted_model M x M' ==> !n. n < LENGTH (listOfN l) ==> nel n l IN M.frame.world``,
rpt strip_tac
>> `LENGTH (listOfN l) > 0` by metis_tac[in_world_LENGTH_at_least_1]
>> `0 < LENGTH (listOfN l)` by fs[]
>> Cases_on `LENGTH (listOfN l) = 1`
  >- (`∃x. l = ncons x 0` by metis_tac[ncons_x_0_LENGTH_1]
    >> `x' = x` by metis_tac[in_world_LENGTH_1_ncons_x_0]
    >> `n = 0` by simp[]
    >> `nel n l = nel 0 (ncons x' 0)` by rw[]
    >> `nel 0 (ncons x' 0) = x'` by simp[nel_ncons_singl]
    >> `x IN M.frame.world` suffices_by metis_tac[]
    >> `x IN M'.frame.world` by metis_tac[rooted_model_def]
    >> `(RESTRICT M'.frame.rel M'.frame.world)^* x x` by metis_tac[RTC_REFL]
    >> metis_tac[rooted_model_def])
  >- (`LENGTH (listOfN l) > 1` by fs[]
    >> `n - 1 < LENGTH (listOfN l) - 1`  by fs[]
    >> `RESTRICT M.frame.rel M.frame.world (nel (n - 1) l)
                   (nel ((n - 1) + 1) l)` by fs[bounded_preimage_rooted_def,IN_DEF]
    >> `(nel (n − 1 + 1) l) IN M.frame.world` by metis_tac[RESTRICT_def]
    >> Cases_on `n >= 1`
      >- (`n - 1 + 1 = n` by simp[]
      >> fs[])
      >- (`n = 0` by simp[]
      >> `nhd l = x` by fs[bounded_preimage_rooted_def]
      >> `x IN M.frame.world` by metis_tac[root_in_rooted_model]
      >> `nel 0 l = nhd l` suffices_by rw[]
      >> metis_tac[nel_nhd]))
);


val nlast_in_world = store_thm(
"nlast_in_world",
``(w ∈ (bounded_preimage_rooted M x).frame.world /\ rooted_model M x M') ==> (nlast w) IN M.frame.world``,
rpt strip_tac
>> `nel (LENGTH (listOfN w) − 1) w IN M.frame.world` suffices_by simp[nlast_nel]
>> `LENGTH (listOfN w) > 0` by metis_tac[in_world_LENGTH_at_least_1]
>> `LENGTH (listOfN w) - 1 < LENGTH (listOfN w)` by fs[]
>> metis_tac[nel_in_M_world]);



val napp_el_in_world = store_thm(
"napp_el_in_world",
``(rooted_model M x M' /\
  w ∈ (bounded_preimage_rooted M x).frame.world /\
  v' ∈ M.frame.world /\
  M.frame.rel (nlast w) v') ==>
  napp w (nlist_of [v']) ∈ (bounded_preimage_rooted M x).frame.world``,
rpt strip_tac
>> rw[bounded_preimage_rooted_def]
  >- (`w <> 0` by metis_tac[in_world_not_zero]
    >> `nhd w = x` by fs[bounded_preimage_rooted_def]
    >> simp[nhd_napp])
  >- (Cases_on `m < LENGTH (listOfN w) - 1`
    >- (`m + 1 < LENGTH (listOfN w)` by fs[]
      >> `m < LENGTH (listOfN w)` by fs[]
      >> `nel m (napp w (ncons v' 0)) = nel m w` by simp[nel_napp]
      >> `nel (m + 1) (napp w (ncons v' 0)) = nel (m + 1) w` by simp[nel_napp]
      >> fs[bounded_preimage_rooted_def])
    >- (`m >= LENGTH (listOfN w) - 1` by fs[]
      >> `LENGTH (listOfN (napp w (ncons v' 0))) = LENGTH (listOfN w) + 1` by simp[LENGTH_napp_singl]
      >> `m < LENGTH (listOfN w)` by simp[]
      >> `m = LENGTH (listOfN w) − 1` by fs[]
      >> `nel m (napp w (ncons v' 0)) = nel m w` by simp[nel_napp]
      >> `_ = nlast w` by simp[nlast_nel]
      >> `nel (LENGTH (listOfN w)) (napp w (ncons v' 0)) = v'` by simp[nel_napp_l2_singl]
      >> `(nlast w) IN M.frame.world` by metis_tac[nlast_in_world]
      >> fs[RESTRICT_def]))
);



val napp_rel = store_thm(
"napp_rel",
``(rooted_model M x M' /\
  w ∈ (bounded_preimage_rooted M x).frame.world /\
  v' ∈ M.frame.world /\
  M.frame.rel (nlast w) v') ==>
  (bounded_preimage_rooted M x).frame.rel w (napp w (nlist_of [v']))``,
rpt strip_tac
>> rw[bounded_preimage_rooted_def]
>- (`ncons v' 0 <> 0` by simp[ncons_not_nnil]
  >> `nlast (napp w (ncons v' 0)) = nlast (ncons v' 0)` by simp[nlast_napp]
  >> `nlast (ncons v' 0) = v'` by simp[Once nlast_def]
  >> simp[RESTRICT_def] >> metis_tac[nlast_in_world])
>- (`nlen w = LENGTH (listOfN w)` by simp[] >> metis_tac[nel_napp]));
  


val root_in_model = store_thm(
"root_in_model",
``rooted_model M x M' ==> ncons x 0 ∈ (bounded_preimage_rooted M x).frame.world``,
rw[bounded_preimage_rooted_def]);



val rooted_model_RTC_eq = store_thm(
"rooted_model_RTC_eq",
``!x x'. RTC (RESTRICT M'.frame.rel M'.frame.world) x x' ==> (rooted_model M x M' ==> (RESTRICT M.frame.rel M.frame.world)^* x x')``,
ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> rpt strip_tac >- metis_tac[RTC_CASES1]
>- (`RESTRICT M.frame.rel M.frame.world x' x''` suffices_by metis_tac[RTC_CASES2] >>
   `x' IN M'.frame.world` by metis_tac[RESTRICT_def] >>
   `x'' IN M'.frame.world` by metis_tac[RESTRICT_def] >>
   `(RESTRICT M'.frame.rel M'.frame.world)^* x x''` by metis_tac[RTC_CASES2] >>
   `x' IN M.frame.world` by metis_tac[rooted_model_def] >>
   `x'' IN M.frame.world` by metis_tac[rooted_model_def] >>
   metis_tac[rooted_model_def,RESTRICT_def]));



val rooted_model_linked_via_RTC = store_thm(
"rooted_model_linked_via_RTC",
``rooted_model M x M' /\ x' IN M.frame.world ==> (RESTRICT M.frame.rel M.frame.world)^* x x'``,
rpt strip_tac
>> `(RESTRICT M'.frame.rel M'.frame.world)^* x x'` by metis_tac[rooted_model_def]
>> metis_tac[rooted_model_RTC_eq]);



val in_model_unique_pred = store_thm(
"in_model_unique_pred",
``!x y. RTC (RESTRICT M.frame.rel M.frame.world) x y ==> (!M'. rooted_model M x M' ==> ∃n. n ∈ (bounded_preimage_rooted M x).frame.world ∧ nlast n = y)``,
ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> rpt strip_tac
>- (qexists_tac `ncons x 0` >> rpt strip_tac >- metis_tac[root_in_model] >> simp[Once nlast_def])
>- (`∃n. n ∈ (bounded_preimage_rooted M x).frame.world ∧ nlast n = y` by metis_tac[]
  >> qexists_tac `napp n (nlist_of [y'])` >> rpt strip_tac
    >- (irule napp_el_in_world
      >- metis_tac[RESTRICT_def]
      >- metis_tac[]
      >- metis_tac[RESTRICT_def]
      >- (qexists_tac `M'` >> rw[]))
    >- simp[nlast_napp_singl]));


val prop_2_15_half2 = store_thm(
"prop_2_15_half2",
``!x M M'. rooted_model M x M' ==> bounded_mor_image nlast (bounded_preimage_rooted M x) M``,
rpt strip_tac >> rw[bounded_mor_image_def]
(* definition of bounded mor image expanded, gives 2 subgoals *)
(* first subgoal: nlast is indeed a bounded mor *)
>- (rw[bounded_mor_def]
  (* definition of bounded_mor expanded, gives 4 subgoals *)
  (* 1. nlast in M.world *)
  >- (`nel (LENGTH (listOfN w) − 1) w IN M.frame.world` suffices_by simp[nlast_nel]
    >> `LENGTH (listOfN w) > 0` by metis_tac[in_world_LENGTH_at_least_1]
    >> `LENGTH (listOfN w) - 1 < LENGTH (listOfN w)` by fs[]
    >> metis_tac[nel_in_M_world]) 
  (* 2. satis same letters *)
  >- (rw[satis_def]
    >> eq_tac >- (rpt strip_tac >- (`nel (LENGTH (listOfN w) − 1) w IN M.frame.world` suffices_by simp[nlast_nel]
    >> `LENGTH (listOfN w) > 0` by metis_tac[in_world_LENGTH_at_least_1]
    >> `LENGTH (listOfN w) - 1 < LENGTH (listOfN w)` by fs[]
    >> metis_tac[nel_in_M_world])
                                >- fs[IN_DEF,bounded_preimage_rooted_def])
              >- (rpt strip_tac >> fs[IN_DEF,bounded_preimage_rooted_def]))
  (* 3. rel *)
  >- (fs[IN_DEF,bounded_preimage_rooted_def] >> metis_tac[RESTRICT_def])
  (* 4. backward condition *)
  >- (qexists_tac `napp w (nlist_of [v'])` >> rpt strip_tac
    >- metis_tac[napp_el_in_world]
    >- metis_tac[napp_rel]
    >- metis_tac[nlast_napp_singl]))
>- (rw[SURJ_DEF]
  >- metis_tac[nlast_in_world]
  >- (irule in_model_unique_pred
    >- metis_tac[rooted_model_linked_via_RTC]
    >- (qexists_tac `M'` >> simp[]))));
    


val prop_2_15 = store_thm(
"prop_2_15",
``!M x M'. rooted_model M x M' ==> ?f MODEL. bounded_mor_image f MODEL M /\ tree_like_model MODEL``,
rpt strip_tac
>> map_every qexists_tac [`nlast`,`bounded_preimage_rooted M x`]
>> rpt strip_tac
>- metis_tac[prop_2_15_half2]
>- (rw[tree_like_model_def] >> qexists_tac `(nlist_of [x])` >> `x ∈ M.frame.world` by metis_tac[root_in_rooted_model] >> metis_tac[prop_2_15_half1]));



val prop_2_15_strengthen = store_thm(
"prop_2_15",
``!M x M'. rooted_model M x M' ==> ?f MODEL s. bounded_mor_image f MODEL M /\ tree MODEL.frame s /\ f s = x``,
rpt strip_tac
>> map_every qexists_tac [`nlast`,`bounded_preimage_rooted M x`] >> qexists_tac `ncons x 0`
>> rpt strip_tac
>- metis_tac[prop_2_15_half2]
>- (`x ∈ M.frame.world` by metis_tac[root_in_rooted_model] >>
   `tree (bounded_preimage_rooted M x).frame (nlist_of [x])` by metis_tac[prop_2_15_half1] >>
   fs[])
>- fs[Once nlast_def]);


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



val prop_2_15_corollary = store_thm(
  "prop_2_15_corollary",
  ``!M w form. w IN M.frame.world /\ satis M w form ==>
  ?MODEL s. tree MODEL.frame s /\ satis MODEL s form``,
  rw[] >>
  `satis (point_GENSUBMODEL M w) w form` by metis_tac[point_GENSUBMODEL_satis] >>
  `rooted_model (point_GENSUBMODEL M w) w M` by metis_tac[point_GENSUBMODEL_rooted] >>
  `?f MODEL s. bounded_mor_image f MODEL (point_GENSUBMODEL M w) /\ tree MODEL.frame s /\ f s = w` by metis_tac[prop_2_15_strengthen] >>
  qexists_tac `MODEL` >> rw[] >> qexists_tac `s` >> rw[] >>
  fs[bounded_mor_image_def] >>
  `s IN MODEL.frame.world` by metis_tac[tree_def] >> metis_tac[prop_2_14]);
  
  




val _ = export_theory();

