/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import org.junit.Test;

import de.tla2b.util.TestUtil;
import static org.junit.Assert.assertEquals;

public class ModelvaluesTest {

	@Test
	public void TestDifferentSetsOfModelvalues() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c \n" + "=================================";
		final String config = "CONSTANTS \n" + "a = {a1, a2, a3}\n"
				+ "b = {b1, b2, b3}\n" + "c = c";
		StringBuilder sb = TestUtil.translateString(module, config);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {a1, a2, a3}; ENUM2 = {b1, b2, b3}; ENUM3 = {c} \n"
				+ "ABSTRACT_CONSTANTS a, b \n"
				+ "PROPERTIES a = ENUM1 & b = ENUM2 END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestSetIntersectionInConfig() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, any \n"
				+ "=================================";
		final String config = "CONSTANTS \n" + "b = {a, b3} \n"
				+ "any = any \n" + "a = a";
		StringBuilder sb = TestUtil.translateString(module, config);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {a, b3}; ENUM2 = {any} \n"
				+ "ABSTRACT_CONSTANTS b \n" + "PROPERTIES b = ENUM1 END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestSetIntersectionInModule() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c \n"
				+ "ASSUME a = b /\\ c \\in a"
				+ "=================================";
		final String config = "CONSTANTS \n" + "a = {a1, a2} \n"
				+ "b = {b1, b2} \n" + "c = c";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {c, a1, a2, b1, b2} \n"
				+ "ABSTRACT_CONSTANTS a, b \n"
				+ "PROPERTIES a = {a1, a2} & b = {b1, b2} & a = b & c : a END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
