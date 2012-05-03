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
	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/typechecking/modules/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void TestExtends1() throws Exception {
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
