/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.*;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestChoose {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	
	@Test
	public void testChoose() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CHOOSE x \\in {1,2,3}: TRUE \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = CHOOSE({x|x : {1, 2, 3} & TRUE = TRUE}) \n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T);"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
