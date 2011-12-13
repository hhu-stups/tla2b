/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestConstants {

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
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4, k5\n"
				+ "ASSUME k5 = 1 \n"
				+ "def1 == 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, "constants", true);
		System.out.println(sb);
	}

}
