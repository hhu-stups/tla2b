/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class LogicOperatorsTest {
	
	/**********************************************************************
	 * equality and disequality: =, #,
	 **********************************************************************/
	@Test
	public void testEquality() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (k2 = 1)\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k").toString());
		assertEquals("INTEGER", t.getConstantType("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testEqualityError() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = TRUE\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	@Test (expected = TypeErrorException.class)
	public void testEqualityError2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = (1=1)\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	
	/**********************************************************************
	 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
	 **********************************************************************/
	@Test
	public void testLogicOperators() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = (k2 \\land k3) \n"
				+ "=================================";
		
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k").toString());
		assertEquals("BOOL", t.getConstantType("k2").toString());
		assertEquals("BOOL", t.getConstantType("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLogicOperatorsError() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME 1 = (k2 \\land k3) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	/**********************************************************************
	 * Quantification: \A x \in S : P or \E x \in S : P.  
	 **********************************************************************/

	
	@Test 
	public void testQuantification() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S\n"
				+ "ASSUME k = (\\A x \\in S : x = k2) /\\ k2 = 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k").toString());
		assertEquals("INTEGER", t.getConstantType("k2").toString());
		assertEquals("POW(INTEGER)", t.getConstantType("S").toString());
	}
	
	@Test(expected = TypeErrorException.class)
	public void testQuantificationException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\A <<x,y>> \\in {1} : TRUE \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
}
