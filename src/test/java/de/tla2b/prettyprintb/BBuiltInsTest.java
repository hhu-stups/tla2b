/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;

import util.ToolIO;

public class BBuiltInsTest {

	/**********************************************************************
	 * BOOLEAN
	 **********************************************************************/
	@Test
	public void testBoolean() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \\in BOOLEAN\n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE : BOOL \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * String
	 **********************************************************************/
	@Test
	public void testString() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \"abc\" \\in STRING\n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES \"abc\" : STRING \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Bool value: TRUE, FALSE
	 **********************************************************************/
	@Test
	public void testBoolValue() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \n" + "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testBoolValue2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE = FALSE \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = FALSE \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
