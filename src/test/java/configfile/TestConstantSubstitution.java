package configfile;
/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/


import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestConstantSubstitution {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/substitution/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testConstantOverridenByDef() throws Exception {
		ToolIO.reset();
		
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ " foo == 5 \n"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k : INTEGER & k = foo \n"
				+ "DEFINITIONS foo == 5 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
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
