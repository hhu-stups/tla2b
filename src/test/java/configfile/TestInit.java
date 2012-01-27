/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import exceptions.ConfigFileErrorException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestInit {

	private static final String I = FileUtil.separator;
	private static String path = "src" + I + "test" + I + "resources" + I
			+ "configfile" + I;
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void TestConfig() throws Exception {
		ToolIO.setUserDir(path);
		ToolIO.reset();
		final String module = "-------------- MODULE ConfigFile ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, "config", true);
		String expected = fileToString(path + "ConfigFile.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingInit() throws Exception {
		ToolIO.setUserDir(path);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";

		Main.start(module, "config", true);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingNext() throws Exception {
		ToolIO.setUserDir(path);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Inv == c \\in Nat \n" + "=================================";

		Main.start(module, "config", true);
	}

	@Test (expected = ConfigFileErrorException.class)
	public void TestMissingInv() throws Exception {
		ToolIO.setUserDir(path);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n" + "=================================";

		Main.start(module, "config", true);
	}
}
