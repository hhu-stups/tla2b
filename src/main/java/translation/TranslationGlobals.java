/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;


import tla2sany.semantic.FrontEnd;

public interface TranslationGlobals {
	final String VERSION = "1.0.5";
	
	final int USED = FrontEnd.getToolId();
	final int OVERRIDE_SUBSTITUTION_ID = 17;
	final int CONSTANT_OBJECT = 18;
	final int DEF_OBJECT = 19;
	final int PRINT_DEFINITION = 11;
	final int TYPE_ID = 5;
	final int LET_PARAMS_ID = 13;
	final int NEW_NAME = 20;
	
	final String CHOOSE = " CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T)";
	final String IF_THEN_ELSE = " IF_THEN_ELSE(P, a, b) == (%t_.(t_=0 & P = TRUE | a )\\/%t_.(t_=0 & not(P= TRUE) | b ))(0)";

}
