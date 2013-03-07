/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.configfile;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.util.TestUtil;



public class OpArgSubstitutionTest {

	@Test
	public void testConstantWithArgsOverriddenByDef() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_) \n"
				+ "foo(a,b) == a+b \n"
				+ "ASSUME k(1,2) = 3 \n"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo(1, 2) = 3 \n"
				+ "DEFINITIONS foo(a,b) == a + b \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testConstantWithArgsOverriddenByDef2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_)\n"
				+ "def(a,b) == a /\\ b \n"
				+ "ASSUME k(TRUE,TRUE)\n"
				+ "=================================";
		final String config = "CONSTANTS k <- def";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES def(TRUE, TRUE) \n"
				+ "DEFINITIONS def(a,b) == a = TRUE & b = TRUE \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test(expected = FrontEndException.class)
	public void testOpArgNoSubstitutionException() throws Exception {
		final String module = "-------------- MODULE OpArgNode ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "plus(a,b) == a + b \n"
				+ "foo(bar(_,_),a,b) == bar(a,b) \n"
				+ "ASSUME foo(plus, 1,3) = 4 \n"
				+ "=================================";
		TestUtil.translateString(module);
	}

	@Test
	public void testOpArgOverriddenByInfixOp() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_) \n"
				+ "ASSUME k(1,2) \n" + "=================================";
		final String config = "CONSTANTS k <- < ";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n" + "PROPERTIES 1 < 2 \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test (expected = ConfigFileErrorException.class)
	public void TestOverridenDefWrongArityException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo(a, b) == a /\\ b  \n"
				+ "def == TRUE /\\ FALSE \n"
				+ "ASSUME foo(TRUE, FALSE) \n"
				+ "=================================";
		final String config = "CONSTANTS foo <- def";
		TestUtil.translateString(module, config);
	}
	
}
