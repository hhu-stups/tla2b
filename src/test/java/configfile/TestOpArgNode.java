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

public class TestOpArgNode {
	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/configfile/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}
	
	@Test
	public void testOpArgNode() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE OpArgNode ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_) \n"
				+ "VARIABLES c \n"
				+ "foo(a,b) == a+b \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + k(1, 2) \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, "OpArgNode", true);
		String expected = fileToString(path + "OpArgNode.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
