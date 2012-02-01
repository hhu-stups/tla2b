/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
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

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x|x : d & TRUE = TRUE} = {1, 2} \n"
				+ "DEFINITIONS d == {1, 2}"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
