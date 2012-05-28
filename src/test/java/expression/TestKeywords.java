/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import org.junit.Test;
import static org.junit.Assert.*;
import translation.ExpressionTranslator;
import exceptions.TLA2BException;

public class TestKeywords {

	@Test
	public void testTRUE() throws TLA2BException {
		final String expr = "TRUE";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("TRUE", res);
	}
	
	@Test
	public void testFALSE() throws TLA2BException {
		final String expr = "FALSE";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("FALSE", res);
	}
	
	@Test
	public void testNat() throws TLA2BException {
		final String expr = "Nat";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("NATURAL", res);
	}
	
	@Test
	public void testExcept() throws TLA2BException {
		final String expr = "x = [a EXCEPT ![1] = 1]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("x = a <+ {1 |-> 1}", res);
	}
	
	@Test
	public void testCardinality() throws TLA2BException {
		final String expr = "Cardinality({1,2,3})";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("card({1, 2, 3})", res);
	}
	
	@Test
	public void testDom() throws TLA2BException {
		final String expr = "dom = 1";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("dom_1 = 1", res);
	}
	
	@Test
	public void testMinOfSet() throws TLA2BException {
		final String expr = "MinOfSet({2,3,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("min({2, 3, 4})", res);
	}
}
