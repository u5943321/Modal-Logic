
open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOL";

val _ = Datatype`
        fterm = ftv num
	       | ffn num (fterm list);
	fform = fRrel fterm fterm
	       | fVrel 'a fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`;

val fAND_def = Define`
  fAND ff1 ff2 = fDISJ (fNOT ff1) (fNOT ff2)`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

(*


val ST_def = Define`
  (ST x (VAR p) <=> fVrel p (ftv x)) /\
  (ST x (FALSE) <=> fNOT (fEQ (ftv x) (ftv x))) /\
  (ST x (NOT phi) <=> fNOT (ST x phi)) /\
  (ST x (DISJ phi psi) <=> fDISJ (ST x phi) (ST x psi)) /\
  (ST x (DIAM phi) <=> fEXISTS (x + 1) (fAND (fRrel (ftv x) (ftv (x + 1))) (ST (x + 1) phi)))`;

*)



(*

val feval_def = Define`
  (feval M σ (fVrel p (ftv x)) <=> ((σ x) IN M.frame.world /\ M.valt p (σ x))) /\
  (feval M σ (fRrel (ftv x) (ftv y)) <=> (σ x) IN M.frame.world /\ (σ y) IN M.frame.world /\ M.frame.rel (σ x) (σ y)) /\
  (feval M σ (fDISJ ff1 ff2) <=> (feval M σ ff1 \/ feval M σ ff2)) /\
  (feval M σ (fNOT ff) <=> ¬(feval M σ ff)) /\
  (feval M σ (fEXISTS n ff) <=> ?w. w IN M.frame.world /\
                                feval M ((n =+ w)σ) ff) /\
  (feval M σ (fEQ ff1 ff2) <=> ff1 = ff2)`;
  


val fsubst = Define`
  fsubst σ 

val ST_BOX = store_thm(
  "ST_BOX",
  ``ST x (BOX phi) = 

EVAL ``ST x (BOX phi)``

*)





val _ = export_theory();

