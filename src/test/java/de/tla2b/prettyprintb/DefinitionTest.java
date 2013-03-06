/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;

import util.ToolIO;

public class DefinitionTest {

	/**********************************************************************
	 * Definition: foo(a,b) == e
	 **********************************************************************/
	@Test
	public void testDefinition() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo(a) == k = a\n"
				+ "ASSUME foo(1) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER  & foo(1) \n"
				+ "DEFINITIONS foo(a) == k = a \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDefinition2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo(a) == k = a\n"
				+ "ASSUME TRUE = foo(1) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER  & TRUE = bool(foo(1)) \n"
				+ "DEFINITIONS foo(a) == k = a \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}


}
