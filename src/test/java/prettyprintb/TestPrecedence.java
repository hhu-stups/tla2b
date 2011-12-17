/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestPrecedence {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testPrecedence() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 * 3) = 7 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 * 3 = 7 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) * 3 = 9 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (1 + 2) * 3 = 9 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) + 3 = 6 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 + 3 = 6 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence4() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 + 3) = 6 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + (2 + 3) = 6 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}