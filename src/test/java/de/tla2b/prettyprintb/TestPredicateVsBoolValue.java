/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.util.TestUtil;

import util.ToolIO;

public class TestPredicateVsBoolValue {

	@Ignore
	@Test
	public void testInstance() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		String module = "---- MODULE Testing----\n"
				+ "foo == TRUE \n"
				+ "ASSUME foo \n"
				+ "=======";
		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		//TODO
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo \n"
				+ "DEFINITIONS foo == TRUE\n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
