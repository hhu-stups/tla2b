/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import org.junit.BeforeClass;
import org.junit.Test;

import translation.ExpressionTranslator;
import util.ToolIO;

public class TestExprWithVariables {

	@BeforeClass
	public static void beforeClass(){
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	@Test
	public void testSimpleExpr() throws Exception {
		ToolIO.reset();
		final String expr = "a + 2";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
	}
	
}
