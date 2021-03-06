/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.translation.ExpressionTranslator;

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

	@Test
	public void testQuantifier() throws TLA2BException {
		final String expr = "\\E x,z \\in Nat, y \\in Nat: x = y";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals(
				"#x,z,y.(x : NATURAL & z : NATURAL & y : NATURAL & x = y)", res);
	}

	@Test
	public void testFunctions() throws TLA2BException {
		final String expr = "LET" + " f[x \\in 1..10] == x*x\n"
				+ " h == [f EXCEPT ![3] = 6]\n" + "IN	h[3]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}

	@Test
	public void testRecord() throws TLA2BException {
		final String expr = "[[a|->1, b |->TRUE] EXCEPT !.a= @+@]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		// assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}

	@Test
	public void testRecord2() throws TLA2BException {
		final String expr = "r = [a |-> [x|->1,y|->TRUE], b |-> 1] "
				+ "/\\ r2 = [r EXCEPT !.a.x = 2]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		// assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}

	@Test
	public void testFunction3() throws TLA2BException {
		final String expr = "r = [x \\in {1,2,3} |-> [a |-> x] ] \n"
				+ "/\\ r2 = [r EXCEPT ![1].a = 11]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		// assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}

	@Test
	public void testFunction4() throws TLA2BException {
		final String expr = "r = [a |-> [x \\in {1,2,3} |-> x], b |-> 1 ] \n"
				+ "/\\ r2 = [r EXCEPT !.a[2+1] = 11]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		// assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}
	
	
	@Ignore
	@Test
	public void testFunction2() throws TLA2BException {
		final String expr = "LET r[x,y \\in {1,2}] == x+y "
				+ "IN [r EXCEPT ![1][2] = 10]";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		// assertEquals("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", res);
	}

}
