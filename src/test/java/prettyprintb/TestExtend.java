/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.BeforeClass;
import org.junit.Test;
import translation.Main;
import util.FileUtil;
import util.ToolIO;
public class TestExtend {

	private static String path = "src/test/resources/prettyprint/extends/";

	@BeforeClass
	public static void beforeClass() {
		path = path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testExtendConAssign() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS start = 2";

		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS start\n"
				+ "PROPERTIES start = 2 \n" + "DEFINITIONS val == 1\n"
				+ "VARIABLES x\n" + "INVARIANT x : INTEGER\n"
				+ "INITIALISATION x:(x=start)\n"
				+ "OPERATIONS Next_Op = ANY x_n \n"
				+ "WHERE x_n : INTEGER & x_n = x + val\n" + "THEN x := x_n END\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testExtendModConAssign() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS start = [Counter] 2";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS start\n"
				+ "PROPERTIES start = 2 \n" + "DEFINITIONS val == 1\n"
				+ "VARIABLES x\n" + "INVARIANT x : INTEGER\n"
				+ "INITIALISATION x:(x=start)\n"
				+ "OPERATIONS Next_Op = ANY x_n \n"
				+ "WHERE x_n : INTEGER & x_n = x + val\n" + "THEN x := x_n END\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}