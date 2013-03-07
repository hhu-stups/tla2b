/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;

import util.ToolIO;

public class TestMiscellaneousConstructs {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testIfThenElse() throws Exception {
		ToolIO.reset();
		final String module = "---WHERE c_n : INTEGER & c_n = c + foo(1,2)----------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = IF 1 = 1 THEN 1 ELSE 2 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER & k = IF_THEN_ELSE(bool(1 = 1), 1, 2) \n"
				+ "DEFINITIONS IF_THEN_ELSE(P, a, b) == (%t_.(t_=TRUE & P = TRUE | a )\\/%t_.(t_=TRUE & not(P= TRUE) | b ))(TRUE); \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testIfThenElse2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = IF 1 = 1 THEN TRUE ELSE FALSE \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : BOOL & k = bool( (1 = 1 => TRUE = TRUE) & (not(1=1) => FALSE = TRUE )) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testIfThenElse3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = IF 1 = 1 THEN 1 ELSE 2 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER & k = IF_THEN_ELSE(bool(1 = 1), 1, 2) \n"
				+ "DEFINITIONS IF_THEN_ELSE(P, a, b) == (%t_.(t_=TRUE & P = TRUE | a )\\/%t_.(t_=TRUE & not(P= TRUE) | b ))(TRUE)"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testIfThenElse4() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ " bar == IF 1= 1 THEN 2 ELSE 4 \n"
				+ " bazz == IF 1= 2 THEN 7 ELSE 8 \n"
				+ " foo == IF 1 = 2 THEN bar ELSE bazz \n"
				+ "ASSUME k = IF 1 = 1 THEN 1 ELSE foo \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER & k = IF_THEN_ELSE(bool(1 = 1), 1, foo) \n"
				+ "DEFINITIONS IF_THEN_ELSE(P, a, b) == (%t_.(t_=TRUE & P = TRUE | a )\\/%t_.(t_=TRUE & not(P= TRUE) | b ))(TRUE);"
				+ " bar == IF_THEN_ELSE(bool(1 = 1), 2, 4); \n"
				+ " bazz == IF_THEN_ELSE(bool(1 = 2), 7, 8); \n"
				+ " foo == IF_THEN_ELSE(bool(1 = 2), bar, bazz) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testCase() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CASE 1 = 1 -> 1 [] 2 = 1 -> 2 [] 0 = 1 -> 3  \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = (%t_.(t_ = 0 & 1 = 1 | 1) \\/ %t_.(t_ = 0 & 2 = 1 | 2) \\/ %t_.(t_ = 0 & 0 = 1 | 3))(0) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testCase2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CASE 1 = 1 \\/ 5 = 6 -> 1 [] 2 = 1  -> 2 [] OTHER -> 3  \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = (%t_.(t_ = 0 & (1 = 1 or 5 = 6) | 1) \\/ %t_.(t_ = 0 & 2 = 1 | 2) \\/ %t_.(t_ = 0 & not(1 = 1 or 5 = 6 or 2 = 1) | 3))(0) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
