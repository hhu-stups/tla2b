/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestRecursiveFunktions {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	/**********************************************************************
	 * Set Enumeration: {1,2,3}
	 **********************************************************************/

	@Test
	public void testIfThenElse() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "foo[a \\in Nat] == IF a = 0 THEN 0 ELSE a + foo[a-1]\n"
				+ "ASSUME k[3] = 6"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
//		final String expected = "MACHINE Testing\n"
//				+ "PROPERTIES foo(1, 2) = 3 \n"
//				+ "DEFINITIONS foo(a,b) == a + b \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
