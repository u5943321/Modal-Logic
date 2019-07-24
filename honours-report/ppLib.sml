structure ppLib =
struct

local open HolKernel Parse boolLib chap2_1Theory chap2_2Theory chap2_3Theory chap2_5Theory chap2_6Theory
           IBCDNFrevisedTheory
in

val _ = temp_remove_termtok { tok = "=", term_name ="="}
val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                       paren_style = OnlyIfNecessary,
		       fixity = Infix(NONASSOC, 450),
		       term_name = "=",
		       pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2),
		                      BeginFinalBlock(PP.CONSISTENT, 2)]}

val _ = temp_remove_termtok { tok = "⇔", term_name ="<=>"}
val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                       paren_style = OnlyIfNecessary,
		       fixity = Infix(NONASSOC, 100),
		       term_name = "<=>",
		       pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,2),
		                      BeginFinalBlock(PP.CONSISTENT, 2)]}



end (* local *)

end (* struct *)
