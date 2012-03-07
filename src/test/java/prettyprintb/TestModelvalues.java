/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;
import translation.Main;
import util.ToolIO;

public class TestModelvalues {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void TestDifferentSetsOfModelvalues() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c \n" + "=================================";
		final String config = "CONSTANTS \n" + "a = {a1, a2, a3}\n"
				+ "b = {b1, b2, b3}\n" + "c = c";
		StringBuilder sb = Main.start(module, config, true);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {a1, a2, a3}; ENUM2 = {b1, b2, b3}; ENUM3 = {c} \n"
				+ "ABSTRACT_CONSTANTS a, b \n"
				+ "PROPERTIES a = ENUM1 & b = ENUM2 END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestSetIntersectionInConfig() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, any \n" + "=================================";
		final String config = "CONSTANTS \n" + "b = {a, b3} \n"
				+ "any = any \n" + "a = a";
		StringBuilder sb = Main.start(module, config, true);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {a, b3}; ENUM2 = {any} \n"
				+ "ABSTRACT_CONSTANTS b \n"
				+ "PROPERTIES b = ENUM1 END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestSetIntersectionInModule() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c \n" 
				+ "ASSUME a = b /\\ c \\in a"
				+ "=================================";
		final String config = "CONSTANTS \n" + "a = {a1, a2} \n"
				+ "b = {b1, b2} \n" + "c = c";
		StringBuilder sb = Main.start(module, config, true);
		String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {c, a1, a2, b1, b2} \n"
				+ "ABSTRACT_CONSTANTS a, b \n"
				+ "PROPERTIES a = {a1, a2} & b = {b1, b2} & a = b & c : a END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
