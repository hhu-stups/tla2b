/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import tla2sany.semantic.FrontEnd;

public interface TranslationGlobals {
	final int USED = FrontEnd.getToolId();
	final int OVERRIDE_SUBSTITUTION_ID = 17;
	final int CONSTANT_OBJECT = 18;
	final int DEF_OBJECT = 19;
	final int PRINT_DEFINITION = 11;
	final int TYPE_ID = 5;
	
	final String CHOOSE = " CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T),T);";
}
