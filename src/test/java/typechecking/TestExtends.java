/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.FileUtil;
import util.ToolIO;
import util.TypeCheckerTest;

public class TestExtends {

	private static final String I = FileUtil.separator;
	private static String path = "src" + I + "test" + I + "resources" + I
			+ "typechecking" + I + "modules" + I;
	static {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void TestNamedInstance() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Counter"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.variables.get("x").toString());
		assertEquals("INTEGER", t.constants.get("start").toString());
	}
}
