package de.tla2b.expression;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.translation.ExpressionTranslator;

public class ModuleTLA2BTest {

	@Test
	public void testMin() throws TLA2BException {
		final String expr = "MinOfSet({3,5,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("min({3, 5, 4})", res);
	}
	
	@Test
	public void testMax() throws TLA2BException {
		final String expr = "MaxOfSet({3,5,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		assertEquals("max({3, 5, 4})", res);
	}
	
	@Test
	public void testSetSummation() throws TLA2BException {
		final String expr = "SetSummation({3,5,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("SIGMA(z_).(z_:{3, 5, 4}|z_)", res);
	}
	
	@Test
	public void testSetProduct() throws TLA2BException {
		final String expr = "SetProduct({3,5,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("PI(z_).(z_:{3, 5, 4}|z_)", res);
	}
	
	@Test
	public void testPermutedSequences() throws TLA2BException {
		final String expr = "PermutedSequences({3,5,4})";
		String res = ExpressionTranslator.translateExpression(expr);
		System.out.println(res);
		assertEquals("perm({3, 5, 4})", res);
	}
}
