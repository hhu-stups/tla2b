/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import exceptions.TypeErrorException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestOverrides {
	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/configfile/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test 
	public void testOverrinding() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE overrides ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "VARIABLES c \n"
				+ "foo == 5 \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + k \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, "overrides", true);
		System.out.println(sb);
		String expected = fileToString(path + "overrides.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test (expected = TypeErrorException.class)
	public void testOverrindingException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "VARIABLES c \n"
				+ "foo == TRUE \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + k \n"
				+ "=================================";
		Main.start(module, "overrides", true);
	}
	
	
}
