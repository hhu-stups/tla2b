/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class TestModuleFiniteSets {

	/**********************************************************************
	 * IsFiniteSet
	 **********************************************************************/
	@Test
	public void unifyIsFiniteSet() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = IsFiniteSet({1,2,3}) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}

	@Test
	public void unifyIsFiniteSet2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = IsFiniteSet(k2) /\\ k2 = {1} \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));

	}

	@Test
	public void unifyIsFiniteSet3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = IsFiniteSet({}) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorIsFiniteSet() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME IsFiniteSet(1)\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorIsFiniteSet2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME 1 = IsFiniteSet({1})\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Cardinality
	 **********************************************************************/
	@Test
	public void unifyCardinality() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Cardinality({1,2,3}) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
	}

	@Test
	public void unifyCardinality2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Cardinality(k2) /\\ k2 = {1} \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorCardinality() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME Cardinality(1)\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorCardinality2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME TRUE = Cardinality({1})\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
