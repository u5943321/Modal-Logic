open HolKernel Parse boolLib bossLib;
open combinTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;


val _ = ParseExtras.tight_equality()

val _ = new_theory "FOLcompactnessJH";


val _ = Datatype`
        fterm = V num
	       | Fn num (fterm list) ;
	fform = fFALSE
	       | fR num fterm fterm
	       | fP num fterm
	       | fIMP fform fform
	       | fFORALL num fform
               | fEXISTS num fform`


val fNOT_def = Define`
  fNOT ff = fIMP ff fFALSE`

val ELIM_fEXISTS_def = Define`
  ELIM_fEXISTS fFALSE = fFALSE /\
  ELIM_fEXISTS (fR a t1 t2) = fR a t1 t2 /\
  ELIM_fEXISTS (fP a t) = fP a t /\
  ELIM_fEXISTS (fIMP ff1 ff2) = fIMP (ELIM_fEXISTS ff1) (ELIM_fEXISTS ff2) /\
  ELIM_fEXISTS (fFORALL n ff) = fFORALL n (ELIM_fEXISTS ff) /\
  ELIM_fEXISTS (fEXISTS n ff) = fNOT (fFORALL n (fNOT ff))`

val tvars_def = tDefine "tvars" `
  tvars (V a) = {a} /\
  tvars (Fn a ts) = BIGUNION (set (MAP tvars ts))
` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` >>
     simp[definition "fterm_size_def"] >> rpt strip_tac >> rw[] >>
     fs[])

val tfns_def = tDefine "tfns" `
  tfns (V a) = {} /\
  (tfns (Fn a ts) = (a, LENGTH ts) INSERT (BIGUNION (set (MAP tfns ts))))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffns_def = Define`
  ffns fFALSE = {} /\
  ffns (fR a ft1 ft2) = (tfns ft1) ∪ (tfns ft2) /\ 
  ffns (fP a ft) = tfns ft /\
  ffns (fIMP ff1 ff2) = (ffns ff1) ∪ (ffns ff2) /\
  ffns (fFORALL n ff) = ffns ff /\
  ffns (fEXISTS n ff) = ffns ff`;

val fprs_def = Define`
  fprs fFALSE = {} /\
  fprs (fR a ft1 ft2) = {(a,2)} /\
  fprs (fP a ft) ={(a,1)} /\
  fprs (fIMP ff1 ff2) = (fprs ff1) ∪ (fprs ff2) /\
  fprs (fFORALL n ff) = fprs ff /\
  fprs (fEXISTS n ff) = fprs ff`;

val fns_def = Define`
  fns fms = BIGUNION {ffns f| f IN fms}`;

val prs_def = Define`
  prs fms = BIGUNION {fprs f| f IN fms}`;

val language_def = Define`
  language fms = (fns fms, prs fms)`;

val tfvs_def = tDefine "tfvs" `
  tfvs (V x) = {x} /\
  tfvs (Fn a ts) = BIGUNION (set (MAP tfvs ts))
  ` (WF_REL_TAC `measure fterm_size` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val ffvs_def = Define`
  ffvs fFALSE = {} /\
  ffvs (fR a ft1 ft2) = (tfvs ft1) ∪ (tfvs ft2) /\
  ffvs (fP a ft) = tfvs ft /\
  ffvs (fIMP ff1 ff2) = (ffvs ff1) ∪ (ffvs ff2) /\
  ffvs (fFORALL n ff) = (ffvs ff) DELETE n /\
  ffvs (fEXISTS n ff) = (ffvs ff) DELETE n`

val tsubst_def = tDefine "tsubst" `
  tsubst v (V x) = v x /\
  tsubst v (Fn a ts) = Fn a (MAP (tsubst v) ts)
  ` (WF_REL_TAC `measure (fterm_size o SND)` >> rpt gen_tac >> Induct_on `ts` 
     >- simp[definition "fterm_size_def"]
     >- (simp[definition "fterm_size_def"] >> rw[]
        >- fs[]
        >> first_x_assum drule >> rw[]))

val VARIANT_def = Define`
  VARIANT vs = (MAX_SET vs) + 1`;


val fsubst_def = Define`
  fsubst v fFALSE = fFALSE /\
  fsubst v (fR a ft1 ft2) = fR a (tsubst v ft1) (tsubst v ft2) /\
  fsubst v (fP a ft) = fP a (tsubst v ft) /\
  fsubst v (fIMP ff1 ff2) = fIMP (fsubst v ff1) (fsubst v ff2) /\
  (fsubst v (fFORALL n ff) = if (?y. y IN (ffvs (fFORALL n ff)) /\ n IN tfvs ((n =+ V n) v y))
                               then (fFORALL (VARIANT (ffvs (fsubst ((n =+ V n) v) ff))) (fsubst ((n =+ V n) v) ff))
			    else (fFORALL n (fsubst ((n =+ V n) v) ff))) /\
  fsubst v (fEXISTS n ff) = if (?y. y IN (ffvs (fEXISTS n ff)) /\ n IN tfvs ((n =+ V n) v y))
                               then (fEXISTS (VARIANT (ffvs (fsubst ((n =+ V n) v) ff))) (fsubst ((n =+ V n) v) ff))
			    else (fEXISTS n (fsubst ((n =+ V n) v) ff))`

val qfree_def = Define`
  (qfree fFALSE = T) /\
  (qfree (fR a t1 t2) = T) /\
  (qfree (fP a t) = T) /\
  (qfree (fIMP ff1 ff2) = (qfree ff1 /\ qfree ff2)) /\
  (qfree (fFORALL n ff) = F) /\
  qfree (fEXISTS n ff) = F `;
val _ = export_rewrites ["qfree_def"]

val (prenex_rules, prenex_ind, prenex_cases) = Hol_reln`
  (!ff. qfree ff ==> prenex ff) /\
  (!ff n. prenex ff ==> prenex (fEXISTS n ff)) /\
  (!ff n. prenex ff ==> prenex (fFORALL n ff))`

val (universal_rules, universal_ind, universal_cases) = Hol_reln`
  (!ff. qfree ff ==> universal ff) /\
  (!ff n. prenex ff ==> universal (fFORALL n ff))`


val size_def = Define`
  size fFALSE = 1 /\
  size (fR a t1 t2) = 1 /\
  size (fP a f) = 1 /\
  (size (fIMP ff1 ff2) = size ff1 + size ff2) /\
  size (fFORALL n ff) = size ff + 1 /\
  size (fEXISTS n ff) = size ff + 3`


  
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
Prenex_right p fFALSE = fIMP p fFALSE /\
Prenex_right p (fR a t1 t2) = fIMP p (fR a t1 t2) /\
Prenex_right p (fP a t) = fIMP p (fP a t) /\
Prenex_right p (fIMP ff1 ff2) = fIMP p (fIMP ff1 ff2) /\
(Prenex_right p (fFORALL n ff) = let y = VARIANT ((ffvs (fFORALL n ff) ∪ (ffvs p))) in
				    fFORALL y (Prenex_right p (fsubst ((n =+ V y) V) ff))) /\
Prenex_right p (fEXISTS n ff) = let y = VARIANT ((ffvs (fEXISTS n ff) ∪ (ffvs p))) in
				    fEXISTS y (Prenex_right p (fsubst ((n =+ V y) V) ff))`
 (WF_REL_TAC `measure (size o SND)` >> rw[] (* 2 *)
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fEXISTS n ff) ∪ ffvs p))⦈ ff) = size ff`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[])
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n ff) ∪ ffvs p))⦈ ff) = size ff`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[]))



val Prenex_left_def = tDefine "Prenex_left" `
Prenex_left fFALSE p = Prenex_right fFALSE p /\
Prenex_left (fR a t1 t2) p = Prenex_right (fR a t1 t2) p /\
Prenex_left (fP a t) p = Prenex_right (fP a t) p /\
Prenex_left (fIMP ff1 ff2) p = Prenex_right (fIMP ff1 ff2) p /\
(Prenex_left (fFORALL n q) p = let y = VARIANT ((ffvs (fFORALL n q) ∪ (ffvs p))) in
				  fEXISTS y (Prenex_left (fsubst ((n =+ V y) V) q) p)) /\
Prenex_left (fEXISTS n q) p = let y = VARIANT ((ffvs (fEXISTS n q) ∪ (ffvs p))) in
				  fFORALL y (Prenex_left (fsubst ((n =+ V y) V) q) p)`
(WF_REL_TAC `measure (size o FST)` >> rw[] (* 2 *)
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fEXISTS n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[])
     >- (`size (fsubst V⦇n ↦ V (VARIANT (ffvs (fFORALL n q) ∪ ffvs p))⦈ q) = size q`
          by metis_tac[size_fsubst] >> rw[size_def] >> fs[]))


val (sshape_rules, sshape_ind, sshape_cases) = Hol_reln`
  sshape (fR a1 t1 u1) (fR a2 t2 u2) /\
  sshape (fP a1 t1) (fP a2 t2) /\
  (sshape f1 f1' /\ sshape f2 f2' ==> sshape (fIMP f1 f2) (fIMP f1' f2')) /\
  (sshape f1 f2 ==> sshape (fFORALL n1 f1) (fFORALL n2 f2)) /\ 
  (sshape f1 f2 ==>  sshape (fEXISTS n1 f1) (fEXISTS n2 f2)) /\
  (sshape fFALSE fFALSE)
`; 

Theorem sshape_vsubst : 
  ∀f s. sshape f (fsubst s f)
Proof
  Induct_on `f` >> simp[fsubst_def] >> rw[] >> simp[sshape_rules]
QED



val qfree_Prenex_left = store_thm(
  "qfree_Prenex_left",
``!f1. qfree f1 ==> !f2. qfree f2 ==> Prenex_left f1 f2 = fIMP f1 f2``,
Induct_on `f1` >> rw[] 

val Prenex_left_subst_subgoal2_1 = store_thm(
  "Prenex_left_subst_subgoal2_1",
``!f2 n f f0. prenex (Prenex_right (fR n f f0) f2) <=> prenex (Prenex_right (fR n (tsubst v f) (tsubst v f0)) f2)``,
Induct_on `f2` (* 6 *)
>- fs[Prenex_right_def] >> rw[] cheat
>- cheat
>- cheat
>- rw[Prenex_right_def]
   (* prenex (fIMP (fR n f f0) (fIMP f2 f2')) is prenex, so must qfree*)  cheat
>- rw[Prenex_right_def]
>- `prenex (Prenex_right (fR n' f f0)
                 (fsubst
                    V⦇n ↦
                       V (VARIANT (ffvs (fFORALL n f2) ∪ ffvs (fR n' f f0)))⦈
                    f2))` by cheat >>
   `prenex (Prenex_right (fR n' (tsubst v f) (tsubst v f0))
           (fsubst
              V⦇n ↦
                 V
                   (VARIANT
                      (ffvs (fFORALL n f2) ∪
			    ffvs (fR n' (tsubst v f) (tsubst v f0))))⦈ f2))` suffices_by cheat >>
   `

val Prenex_right_qfree = store_thm(
	"Prenex_right_qfree",
	``!f1 f2. qfree f1 ==> 











val Prenex_left_subst = store_thm(
  "Prenex_left_subst",
``!f1 f2. prenex (Prenex_left f1 f2) ==> !v. prenex (Prenex_left (fsubst v f1) f2)``,	
Induct_on `f1` >> rw[] (* 6 *)
	  >- (* if LHS is qfree then prenex (Prenex_left f1' f2) *) fs[fsubst_def]
	  >- fs[fsubst_def] >> fs[Prenex_left_def,Prenex_right_def] >> Cases_on `f2` (* 6 *)
             >- fs[Prenex_right_def]






				 ] >> Induct_on `f2` (* 6 *)
             >- (rw[Prenex_left_def,Prenex_right_def,fsubst_def] >>
                `qfree (fIMP (fR n (tsubst v f) (tsubst v f0)) fFALSE)` suffices_by metis_tac[prenex_rules] >>
                fs[qfree_def])
             >- (rw[Prenex_left_def,Prenex_right_def,fsubst_def] >>
                `qfree (fIMP (fR n (tsubst v f) (tsubst v f0)) (fR n' f' f0'))` suffices_by metis_tac[prenex_rules] >>
                fs[qfree_def])
             >- (rw[Prenex_left_def,Prenex_right_def,fsubst_def] >>
                `qfree (fIMP (fR n (tsubst v f) (tsubst v f0)) (fP n' f'))` suffices_by metis_tac[prenex_rules] >>
                fs[qfree_def])
             >- rw[] >> fs[fsubst_def,Prenex_left_def,Prenex_right_def] >> 
                (*(fIMP (fR n f f0) (fIMP f2 f2')) is qfree so subst is qfree*) >> cheat

	     >- `prenex (Prenex_right (fR n (tsubst v f) (tsubst v f0))
           (fsubst
              V⦇n' ↦
                 V
                   (VARIANT
                      (ffvs (fFORALL n' f2) ∪
                       ffvs (fR n (tsubst v f) (tsubst v f0))))⦈ f2))` suffices_by cheat >>
                `prenex (Prenex_right (fR n f f0)
                 (fsubst
                    V⦇n' ↦
                       V (VARIANT (ffvs (fFORALL n' f2) ∪ ffvs (fR n f f0)))⦈
                    f2))` by cheat >> Induct_on 



	     


	  >- cheat
          >- fs[Prenex_left_def] (* if prenex (fIMP (fIMP f1 f1') f2) then it cannot have any quantifier, so suffices to prove subst does not add quantifiers. *)
	  >- fs[Prenex_left_def] >> Induct_on `f2` >> rw[] (* 6 *)
	     >- fs[Prenex_left_def,fsubst_def]


Theorem prenex_rwts[simp]:
  (prenex fFALSE <=> T) /\
  (prenex (fIMP f1 f2) <=> qfree f1 /\ qfree f2) /\
  (prenex (fR a t1 t2) <=> T) /\
  (prenex (fP a t) <=> T) /\
  (prenex (fEXISTS n f) <=> prenex f) /\
  (prenex (fFORALL n f) <=> prenex f)
Proof
  rpt conj_tac >> simp[Once prenex_cases, SimpLHS]
QED
			
Theorem qfree_fsubst[simp]:
  !f s. qfree (fsubst s f) <=> qfree f
Proof
  Induct_on `f` >> rw[fsubst_def]
QED

Theorem prenex_fsubst[simp]:
  !f s. prenex (fsubst s f) <=> prenex f
Proof
  Induct_on `f` >> rw[fsubst_def]
QED
	 
Theorem tsubst_composition : 
  (∀t s1 s2. tsubst s1 (tsubst s2 t) = tsubst (tsubst s1 o s2) t) ∧
  (∀tl s1 s2. MAP (\a. tsubst s1 (tsubst s2 a)) tl = MAP (tsubst (tsubst s1 o s2)) tl)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:fterm``) >> 
  simp[tsubst_def, listTheory.MAP_MAP_o] >>
  simp_tac (bool_ss ++ boolSimps.ETA_ss) [] >> 
  rpt strip_tac >> pop_assum (fn th => simp[GSYM th]) >> 
  simp[combinTheory.o_DEF]
QED

(*
    
Theorem fsubst_composition : 
  ∀f s1 s2. fsubst s1 (fsubst s2 f) = fsubst (tsubst s1 o s2) f
Proof
  Induct_on `f` >> simp[fsubst_def, tsubst_composition] >> rw[] 
  >- (qmatch_abbrev_tac `fsubst _ (fFORALL v (fsubst ss f)) = 
                         fFORALL u (fsubst tt f)` >>
      simp[fsubst_def] >> rw[]
      >- simp[Abbr`u`, Abbr`tt`, Abbr`ss`]

*)

Theorem Prenex_right_subst:
  !f1 f2 s. qfree f1 /\ prenex f2 ==> prenex (Prenex_right f1 f2)
Proof					       
  completeInduct_on `size f2` >> fs[PULL_FORALL] >> Cases >> 
  rw[size_def, fsubst_def, Prenex_right_def] 
  >> (first_x_assum irule >> simp[prenex_fsubst, GSYM size_fsubst])
QED
     
val prenex_Prenex_left = store_thm(
  "prenex_Prenex_left",							       
  ``!f1 f2. prenex f1 /\ prenex f2 ==> prenex (Prenex_left f1 f2)``,
  completeInduct_on `size f1` >> fs[PULL_FORALL] >> Cases >> 
  rw[fsubst_def, Prenex_left_def, Prenex_right_subst] (* 2 *) >>
  first_x_assum irule >> simp[size_def, GSYM size_fsubst]);



	
val Prenex_def = Define`
  Prenex fFALSE = fFALSE /\
  Prenex (fR a t1 t2) = fR a t1 t2 /\
  Prenex (fP a t) = fP a t /\
  Prenex (fIMP ff1 ff2) = Prenex_left (Prenex ff1) (Prenex ff2) /\
  Prenex (fFORALL n p) = fFORALL n (Prenex p) /\
  Prenex (fEXISTS n p) = fEXISTS n (Prenex p)`;




				
val prenex_Prenex = store_thm(
	"prenex_Prenex",
``!ff. prenex (Prenex ff)``,
Induct_on `ff` (* 6 *)
>- (rw[Prenex_def] >> `qfree fFALSE` by fs[qfree_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> `qfree (fR n f f0)` by fs[qfree_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> `qfree (fP n f)` by fs[qfree_def] >> metis_tac[prenex_rules])
>- rw[Prenex_def,prenex_Prenex_left]
>- (rw[Prenex_def] >> metis_tac[prenex_rules])
>- (rw[Prenex_def] >> metis_tac[prenex_rules]));

			       
val _ = export_theory();

