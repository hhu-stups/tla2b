/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;
import org.junit.Test;
import translation.Main;
import util.ToolIO;

public class TestDefinition {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Definition: foo(a,b) == e
	 **********************************************************************/
	@Test
	public void testDefinition() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo(a) == k = a\n"
				+ "ASSUME foo(1) \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER  & foo(1) \n"
				+ "DEFINITIONS foo(a) == k = a \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDefinition2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo(a) == k = a\n"
				+ "ASSUME TRUE = foo(1) \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER  & TRUE = bool(foo(1)) \n"
				+ "DEFINITIONS foo(a) == k = a \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}


}
