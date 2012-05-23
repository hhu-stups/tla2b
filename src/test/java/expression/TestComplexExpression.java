/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package expression;

import org.junit.Test;

import translation.ExpressionTranslator;
import exceptions.TLA2BException;
import static org.junit.Assert.*;
public class TestComplexExpression {

	@Test
	public void testExcept() throws TLA2BException {
		final String expr = "a = [u \\in {3,4,5}|-> u + 1] /\\ x = [a EXCEPT ![3] = 1]";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("a = %u.(u : {3, 4, 5}| u + 1) & x = a <+ {3 |-> 1}", res);
	}
	
	@Test
	public void testLetIn() throws TLA2BException {
		final String expr = "LET foo == 1 IN foo + foo";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("1 + 1", res);
	}
	
	@Test
	public void testLetDefWithArgs() throws TLA2BException {
		final String expr = "LET foo(x,y) == x * y IN foo(2,4) ";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("2 * 4", res);
	}
	
	@Test
	public void testLetTwoDefs() throws TLA2BException {
		final String expr = "LET foo == 1 bar == 2 IN foo + bar ";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("1 + 2", res);
	}
	
	@Test
	public void testPrime() throws TLA2BException {
		final String expr = "x' = 1";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("x_n = 1", res);
	}
	
	@Test
	public void testFunction() throws TLA2BException {
		final String expr = "LET f[n \\in {1}] == 1 IN f[1]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("%n.(n : {1}| 1)(1)", res);
	}
	
}
