/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestConstantOverride {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	@Test
	public void testConstantOverridenByDef() throws Exception {
		ToolIO.reset();
		
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ " foo == 5 \n"
				+ "ASSUME k = 5"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo = 5 \n"
				+ "DEFINITIONS foo == 5 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
