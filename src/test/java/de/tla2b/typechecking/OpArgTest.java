/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;



public class OpArgTest {

	@Test
	public void TestConOverridenByLessOp() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_), k2 \n"
				+ "ASSUME k2 = k(1,2)\n" + "=================================";
		final String config = "CONSTANTS k <- <";
		TestTypeChecker t = TestUtil.typeCheckString(module, config);
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestOverridenConstantWrongArityException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_) \n"
				+ "def == TRUE /\\ FALSE \n"
				+ "=================================";
		final String config = "CONSTANTS k <- def";
		TestUtil.typeCheckString(module, config);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestOverridenDefWrongArityException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo(a, b) == a /\\ b  \n"
				+ "def == TRUE /\\ FALSE \n"
				+ "ASSUME foo(TRUE, FALSE) \n"
				+ "=================================";
		final String config = "CONSTANTS foo <- def";
		TestUtil.typeCheckString(module, config);
	}

	@Test
	public void TestOverridenByDef() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_), k2 \n"
				+ "def(a,b) == a /\\ b \n"
				+ "ASSUME k2 = k(TRUE,TRUE)\n"
				+ "=================================";
		final String config = "CONSTANTS k <- def";
		TestTypeChecker t = TestUtil.typeCheckString(module, config);
		assertEquals("BOOL", t.getConstantType("k2"));
		System.out.println(t.getDefinitionType("def"));
		assertEquals("BOOL", t.getDefinitionType("def"));
		assertEquals("BOOL", t.getDefinitionParamType("def", "a"));
	}
}
