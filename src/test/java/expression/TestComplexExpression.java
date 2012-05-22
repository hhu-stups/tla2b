/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import org.junit.Test;

import translation.ExpressionTranslator;
import exceptions.TLA2BException;

public class TestComplexExpression {


	@Test
	public void testSimpleExpr4() throws TLA2BException {
		final String expr = "a = [u \\in {3,4,5}|-> u + 1] /\\ x = [a EXCEPT ![3] = 1]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
	}
}
