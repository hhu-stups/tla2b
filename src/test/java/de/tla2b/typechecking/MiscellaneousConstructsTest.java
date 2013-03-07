/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class MiscellaneousConstructsTest {

	/**********************************************************************
	 * IF THEN ELSE
	 **********************************************************************/
	@Test
	public void testIfThenElse() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = (IF k2 THEN k3 ELSE k4) /\\ k4 = 1  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER",t.getConstantType("k"));
		assertEquals("BOOL",t.getConstantType("k2"));
		assertEquals("INTEGER",t.getConstantType("k3"));
		assertEquals("INTEGER",t.getConstantType("k4"));
	}
	

	/**********************************************************************
	 * IF THEN ELSE
	 **********************************************************************/
	@Test
	public void testCase() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, e1, e2 \n"
				+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2) /\\ e2 = 1  \n"
				+ "=================================";
		TestTypeChecker t =TestUtil.typeCheckString(module);
		assertEquals("INTEGER",t.getConstantType("k"));
		assertEquals("BOOL",t.getConstantType("k2"));
		assertEquals("BOOL",t.getConstantType("k3"));
		assertEquals("INTEGER",t.getConstantType("e1"));
		assertEquals("INTEGER",t.getConstantType("e2"));
	}
	
	@Test
	public void testCase2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, e1, e2, e3 \n"
				+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2 [] OTHER -> e3) /\\ e2 = 1  \n"
				+ "=================================";
		TestTypeChecker t =TestUtil.typeCheckString(module);
		assertEquals("INTEGER",t.getConstantType("k"));
		assertEquals("BOOL",t.getConstantType("k2"));
		assertEquals("BOOL",t.getConstantType("k3"));
		assertEquals("INTEGER",t.getConstantType("e1"));
		assertEquals("INTEGER",t.getConstantType("e2"));
		assertEquals("INTEGER",t.getConstantType("e3"));
	}
	
	/**********************************************************************
	 * LET d == exp IN e
	 **********************************************************************/
	@Test
	public void testLetIn() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (LET d == k2 IN d = k3) /\\ k2 = 1  \n"
				+ "=================================";
		TestTypeChecker t =TestUtil.typeCheckString(module);
		assertEquals("BOOL",t.getConstantType("k"));
		assertEquals("INTEGER",t.getConstantType("k2"));
		assertEquals("INTEGER",t.getConstantType("k3"));
	}
	
	@Test
	public void testLetIn2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (LET d == k2 d2 == k3 IN d = d2) /\\ k2 = 1  \n"
				+ "=================================";
		TestTypeChecker t =TestUtil.typeCheckString(module);
		assertEquals("BOOL",t.getConstantType("k"));
		assertEquals("INTEGER",t.getConstantType("k2"));
		assertEquals("INTEGER",t.getConstantType("k3"));
	}
	
	@Test
	public void testLetIn3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = (LET d(a,b) == a=k2/\\b=k3 IN d(1,k4)) /\\ k4 = TRUE  \n"
				+ "=================================";
		TestTypeChecker t =TestUtil.typeCheckString(module);
		assertEquals("BOOL",t.getConstantType("k"));
		assertEquals("INTEGER",t.getConstantType("k2"));
		assertEquals("BOOL",t.getConstantType("k3"));
		assertEquals("BOOL",t.getConstantType("k4"));
	}
	
	
}
