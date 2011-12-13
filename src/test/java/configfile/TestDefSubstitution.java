/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
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
	public void testDefSubstitution() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE DefSubstitution ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "foo == 5 \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + foo \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, "DefSubstitution", true);
		String expected = fileToString(path + "DefSubstitution.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test 
	public void testDefOverriding() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE DefOverriding ----------------\n"
				+ "VARIABLES c \n"
				+ "foo == 5 \n"
				+ "foo2 == 6 \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = foo \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, "DefOverriding", true);
		String expected = fileToString(path + "DefOverriding.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
