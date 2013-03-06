/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.translation.ExpressionTranslator;



public class TestError {

	@Test (expected = FrontEndException.class)
	public void testParseError() throws Exception {
		final String expr = "a =";
		ExpressionTranslator.translateExpression(expr);
	}
	
	@Test (expected = FrontEndException.class)
	public void testSemanticError() throws Exception {
		final String expr = "a(1)";
		ExpressionTranslator.translateExpression(expr);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testTypeError() throws Exception {
		final String expr = "1 = TRUE";
		ExpressionTranslator.translateExpression(expr);
	}
}
