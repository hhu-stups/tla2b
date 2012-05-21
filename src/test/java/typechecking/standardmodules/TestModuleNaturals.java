/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking.standardmodules;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;
import exceptions.TypeErrorException;

public class TestModuleNaturals {

	/**********************************************************************
	 * Relational operators: >, <, <=, >=
	 **********************************************************************/
	@Test  
	public void testRelationalOperators() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (k2 > k3) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRelationalOperatorsException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME 1 = (2 > 1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	
	/**********************************************************************
	 * Arithmetic operator: +, -, *, /, mod, exp
	 **********************************************************************/
	@Test  
	public void testArithmeticOperators() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 + k3 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testArithmeticOperatorsException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME TRUE = 1 + 1 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	

	/**********************************************************************
	 * Interval operator: x .. y 
	 **********************************************************************/
	
	@Test  
	public void testDotDot() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 .. k3 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testDotDotException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS  k2, k3 \n"
				+ "ASSUME TRUE \\in  k2 .. k3 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * Nat
	 **********************************************************************/
	@Test  
	public void testNat() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Nat \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void unifyErrorNat() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME TRUE \\in Nat \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
}
