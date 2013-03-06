/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.translation.ExpressionTranslator;


public class TestSequences {

	@Test
	public void testAppend() throws Exception {
		final String expr = "Append(<<1>>, 2)";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("[1] <- 2", res);
	}
	
	@Test
	public void testHead() throws Exception {
		final String expr = "Head(<<1,2,3>>)";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("first([1, 2, 3])", res);
	}
	
	@Test
	public void testTail() throws Exception {
		final String expr = "Tail(<<1,2,3>>)";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("tail([1, 2, 3])", res);
	}
	
}
