/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class testUsedKeyword {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	@Test
	public void testRenamingConstant() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS seq \n"
				+ "ASSUME seq = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS seq_1 \n"
				+ "PROPERTIES seq_1 : INTEGER & seq_1 = 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRenamingVariable() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES seq \n"
				+ "Init == seq = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "VARIABLES seq_1 \n"
				+ "INVARIANT seq_1 : INTEGER\n"
				+ "INITIALISATION seq_1:(seq_1 = 1)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRenamingDefinition() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "seq == 1 = 1 \n"
				+ "ASSUME seq \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES seq_1 \n"
				+ "DEFINITIONS seq_1 == 1 = 1\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRenamingInfixOperator() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals"
				+ " a \\prec b  == a > b \n"
				+ "ASSUME  3 \\prec 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES prec(3, 1) \n"
				+ "DEFINITIONS prec(a,b) == a > b\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
