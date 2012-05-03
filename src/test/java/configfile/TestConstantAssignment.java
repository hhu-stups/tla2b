package configfile;
/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/


import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestConstantAssignment {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	
	@Test
	public void testValueAssignedToConstant() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "=================================";
		final String config = "CONSTANTS k = 1";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k = 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
