/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import org.junit.Test;

import exceptions.FrontEndException;

import translation.ExpressionTranslator;

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
}
