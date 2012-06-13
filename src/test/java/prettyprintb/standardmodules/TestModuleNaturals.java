/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb.standardmodules;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestModuleNaturals {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Relational operators: >, <, <=, >=
	 **********************************************************************/
	@Test
	public void testRelationalOperators() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 < 2 /\\ 2 > 1 /\\ 1 <= 1 /\\ 1 >= 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 < 2 & 2 > 1 & 1 <= 1 & 1 >= 1 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testRelationalOperators2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 < 2) = (2 > 1) /\\ (1 <= 1) = (1 >= 1) \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES bool(1 < 2) = bool(2 > 1) & bool(1 <= 1) = bool(1 >= 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Arithmetic operator: +, -, *, \div, %, ^
	 **********************************************************************/
	@Test
	public void testArithmeticOperators() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + 2 = 4-1 /\\ 1 * 2 = 4 \\div 2 /\\  1 ^ 1 = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 = 4 - 1 & 1 * 2 = 4 / 2 & 1 ** 1 = 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Interval operator: x .. y 
	 **********************************************************************/
	@Test
	public void testDotDot() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 \\in 1 .. 2 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : 1..2 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Nat
	 **********************************************************************/
	@Test
	public void testNat() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 \\in Nat \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : NATURAL \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testMod() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals, Integers \n"
				+ "ASSUME -3 % 2 = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (%t_.( t_ = 0 & -3 < 0 | -(-3) mod 2 )\\/%t_.( t_ = 0 & not(-3<0) | -3 mod 2))(0) = 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
