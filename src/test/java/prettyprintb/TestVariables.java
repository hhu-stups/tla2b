/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestVariables {

	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testSetEnumeration() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
