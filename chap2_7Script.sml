open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open chap2_4revisedTheory;
open chap2_5Theory
open equiv_on_partitionTheory;
open IBCDNFrevisedTheory;
open prim_recTheory;
open listTheory;
open finite_mapTheory;
open combinTheory;

val _ = ParseExtras.tight_equality()

val _ = new_theory "chap2_7";


val sim_def = Define`
  sim Z M M' <=>
  !w w'. w IN M.frame.world /\ w' IN M'.frame.world /\ Z w w' ==>
  (!p. w IN M.valt p ==> w' IN M'.valt p) /\
  (!v. v IN M.frame.world /\ M.frame.rel w v ==> ?v'. v' IN M'.frame.world /\ Z v v' /\ M'.frame.rel w' v')`;

val preserved_under_sim_def = Define`
  preserved_under_sim (μ:'a itself) (ν:'b itself) phi <=> 
  (!M M' Z w w'. w:'a IN M.frame.world /\ w':'b IN M'.frame.world /\ sim Z M M' /\ Z w w' ==> (satis M w phi ==> satis M' w' phi))`;



val (PE_rules, PE_ind, PE_cases) = Hol_reln`
  (!p. PE (VAR p)) /\ 
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (AND f1 f2)) /\ 
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (DISJ f1 f2)) /\
  (!f. PE f ==> PE (DIAM f))`;    


val thm_2_78_half1_lemma = store_thm(
  "thm_2_78_half1_lemma",
  ``!phi. PE phi ==> (!μ ν. preserved_under_sim μ ν phi)``,
   Induct_on `PE phi` >> rw[preserved_under_sim_def] (* 4 *)
   >- (fs[satis_def] >> metis_tac[sim_def])
   >- (fs[satis_AND] >> metis_tac[])
   >- (fs[satis_def] >> metis_tac[])
   >- (fs[satis_def] >> imp_res_tac sim_def >> metis_tac[]));

val thm_2_78_half1 = store_thm(
  "thm_2_78_half1",
  ``!phi phi0 μ ν. (PE phi0 /\ equiv0 μ phi phi0 /\ equiv0 ν phi phi0) ==> preserved_under_sim μ ν phi``,
  rw[] >> `preserved_under_sim μ ν phi0` by metis_tac[thm_2_78_half1_lemma] >>
  fs[preserved_under_sim_def] >> rw[] >> fs[equiv0_def] >> `satis M w phi0` by metis_tac[] >> metis_tac[]);


 Let  be a set of ﬁrst-order formulas. If each ﬁnite subset of  has a model, then  itself has a model.


val compactness_theorem = store_thm(
  "compactness_theorem",
  ``!Σ. (!Σ0. FINITE Σ0 /\ Σ0 ⊆ Σ ==> (?M σ. !f. f IN Σ0 ==> fsatis M σ f)) ==>
         ?M σ. (!f. f IN Σ ==> fsatis M σ f)``,
  

  
  

val thm_2_78_half2 = store_thm(
  "thm_2_78_half2",
  ``!phi μ ν. preserved_under_sim μ ν phi ==> (?phi0. equiv0 μ phi phi0 /\ equiv0 ν phi phi0 /\ PE phi0)``,
  rw[] >>


  