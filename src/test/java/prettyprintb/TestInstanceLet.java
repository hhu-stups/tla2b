/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestInstanceLet {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/instance/";
	static {
		path=path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testInstance() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES c, c2 \n"
				+ "inst == INSTANCE Let WITH x <- c  \n"
				+ "inst2 == INSTANCE Let WITH x <- c2  \n"
				+ "Init == inst!Init /\\ inst2!Init \n"
				+ "Next == inst!Next /\\ inst2!Next\n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
//		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
//				+ "PROPERTIES k : POW(INTEGER) & k = {1,2,3} \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
