/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.BeforeClass;
import org.junit.Test;

import exceptions.ConfigFileErrorException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestInstanceConfOverride {

	
	private static String path = "src/test/resources/prettyprint/extends/";

	@BeforeClass
	public static void beforeClass() {
		path = path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testInstanceDefOverride() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS val =[Counter] 4";

		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS start\n"
				+ "PROPERTIES start : INTEGER \n" + "DEFINITIONS val == 4\n"
				+ "VARIABLES x\n" + "INVARIANT x : INTEGER\n"
				+ "INITIALISATION x:(x=start)\n"
				+ "OPERATIONS Next_Op = ANY x_n \n"
				+ "WHERE x_n : INTEGER & x_n = x + val\n" + "THEN x := x_n END\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceConOverrideException() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" 
				+ "foo == 11 \n"
				+ "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS start <-[Counter] foo";

		Main.start(module, config, true);
	}
	
	
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS a <-[Counter] def";

		Main.start(module, config, true);
	} 
	
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException2() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS val <-[Cou] def";

		Main.start(module, config, true);
	}
	
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException3() throws Exception {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS val <-[Counter] d";

		Main.start(module, config, true);
	}
	
}
