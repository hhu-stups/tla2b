/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestDefSubstitution {
	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/configfile/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	
	@Test 
	public void testValueAssignedToDef() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = 1 \n"
				+ "=================================";
		final String config = "CONSTANTS foo = 1";
		StringBuilder sb = Main.start(module, config, true);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES foo = 1 \n"
				+ "DEFINITIONS foo == 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
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
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES bar = 2 \n"
				+ "DEFINITIONS bar == 2 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
