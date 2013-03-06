/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.Test;

import de.tla2b.translation.ExpressionTranslator;

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
		assertEquals("a + 2", res);
	}
	
}
