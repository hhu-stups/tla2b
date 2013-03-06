/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.translation.Translator;
import de.tla2b.util.Util;

import util.ToolIO;

public class TestUsedDefinitions {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testChoose() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "d == {1,2}"
				+ "ASSUME {x \\in d : TRUE} = {1,2} \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x|x : d & TRUE = TRUE} = {1, 2} \n"
				+ "DEFINITIONS d == {1, 2}"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
