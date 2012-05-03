/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestDefOverride {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test 
	public void testDefOverriddenByDef() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo == 1 \n"
				+ "bar == 2 \n"
				+ "ASSUME foo = 2 \n"
				+ "=================================";
		final String config = "CONSTANTS foo <- bar";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES bar = 2 \n"
				+ "DEFINITIONS bar == 2 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
