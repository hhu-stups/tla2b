/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;
import exceptions.TypeErrorException;

public class TestLogicOperators {
	
	/**********************************************************************
	 * equality and disequality: =, #,
	 **********************************************************************/
	@Test
	public void testEquality() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (k2 = 1)\n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testEqualityError() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = TRUE\n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	@Test (expected = TypeErrorException.class)
	public void testEqualityError2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = (1=1)\n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	
	/**********************************************************************
	 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
	 **********************************************************************/
	@Test
	public void testLogicOperators() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = (k2 \\land k3) \n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLogicOperatorsError() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME 1 = (k2 \\land k3) \n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * Quantification: \A x \in S : P or \E x \in S : P.  
	 **********************************************************************/

	
	@Test 
	public void testQuantification() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S\n"
				+ "ASSUME k = (\\A x \\in S : x = k2) /\\ k2 = 1 \n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}
	
	@Test(expected = TypeErrorException.class)
	public void testQuantificationException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\A <<x,y>> \\in {1} : TRUE \n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
}
