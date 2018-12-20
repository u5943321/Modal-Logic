open HolKernel Parse boolLib bossLib;

val _ = new_theory "FOLSyntax";

val _ = Datatype`
        fterm = fVar num
	       | fConst num ;
	fform = fRrel 'a fterm fterm
	       | fPrel 'a fterm
	       | fDISJ fform fform
	       | fNOT fform
	       | fEXISTS num fform
	       | fEQ fterm fterm`;



val tvars_def = Define`
  tvars (fVar a) = {a} /\
  tvars (fConst a) = {}`;

val fvars_def = Define`
  fvars (fRrel a t1 t2) = tvars t1 ∪ tvars t2 /\
  fvars (fPrel a t) = tvars t /\
  fvars (fDISJ ff1 ff2) = (fvars ff1) ∪ (fvars ff2) /\
  fvars (fNOT ff) = fvars ff /\
  fvars (fEXISTS n ff) = n INSERT (fvars ff) /\
  fvars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val tconsts_def = Define`
  tconsts (fVar a) = {} /\
  tconsts (fConst a) = {a}`;

val fconsts_def = Define`
  fconsts (fRrel a t1 t2) = tconsts t1 ∪ tconsts t2 /\
  fconsts (fPrel a t) = tconsts t /\
  fconsts (fDISJ ff1 ff2) = (fconsts ff1) ∪ (fconsts ff2) /\
  fconsts (fNOT ff) = fconsts ff /\
  fconsts (fEXISTS n ff) = n INSERT (fconsts ff) /\
  fconsts (fEQ t1 t2) = tconsts t1 ∪ tconsts t2`;


val freevars_def = Define`
  freevars (fRrel a t1 t2) = tvars t1 ∪ tvars t2 /\
  freevars (fPrel a t) = tvars t /\
  freevars (fDISJ ff1 ff2) = freevars ff1 ∪ freevars ff2 /\
  freevars (fNOT ff) = freevars ff /\
  freevars (fEXISTS n ff) = freevars ff DELETE n /\
  freevars (fEQ t1 t2) = tvars t1 ∪ tvars t2`;


val fAND_def = Define`
  fAND ff1 ff2 = fNOT (fDISJ (fNOT ff1) (fNOT ff2))`;

val fFORALL_def = Define`
  fFORALL n ff = fNOT (fEXISTS n (fNOT ff))`;

val fIMP_def = Define`
  fIMP ff1 ff2 = fDISJ (fNOT ff1) ff2`;


val _ = export_theory();

