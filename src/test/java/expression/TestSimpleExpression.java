/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import exceptions.TLA2BException;

import translation.ExpressionTranslator;
import util.ToolIO;

public class TestSimpleExpression {

	@Test
	public void testSimpleExpr() throws TLA2BException {
		final String expr = "1 + 2";
		String res = ExpressionTranslator.translateExpression(expr);

	}

	@Test
	public void testSimpleExpr2() throws Exception {
		final String expr = "\\E a \\in {1}: 2 > 1";
		String res = ExpressionTranslator.translateExpression(expr);
	}

	@Test
	public void testSimpleExpr3() throws Exception {
		final String expr = "IF 1 = 1 THEN 1 ELSE 2";
		String res = ExpressionTranslator.translateExpression(expr);
	}

	@Test
	public void testSimpleExpr4() throws TLA2BException {
		final String expr = "TRUE";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
	}
}
