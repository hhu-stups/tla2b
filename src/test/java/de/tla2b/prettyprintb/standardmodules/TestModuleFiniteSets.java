/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class TestModuleFiniteSets {

	@Test
	public void testIsFiniteSet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME IsFiniteSet({1,2,3}) \n"
				+ "=================================";
		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1,2,3} : FIN({1,2,3}) \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testIsFiniteSet2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets, Naturals \n"
				+ "ASSUME IsFiniteSet(Nat) \n"
				+ "=================================";
		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES NATURAL : FIN(NATURAL) \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCardinality() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets, Naturals \n"
				+ "ASSUME Cardinality({1,2,3}) = 3 \n"
				+ "=================================";
		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES card({1,2,3}) = 3 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}
