/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;

import util.ToolIO;

public class TestPrecedence {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testSetConstructor() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME {x \\in {1,2,3} : x \\in {1}  \\/ x \\in {2}} = {1,2} \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x|x : {1, 2, 3} & (x : {1} or x : {2})} = {1, 2} \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 * 3) = 7 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 * 3 = 7 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSetDifference() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS mx \n"
				+ "ASSUME mx=5 \n"
				+ "VARIABLES x\n"
				+ "Init == x = {} \n"
				+ "Invariant == \n"
				+ " x \\subseteq 1..mx \n"
				+ "Addx ==  \\E n \\in (1..mx)\\ x : x' = x \\cup {n} \n"
				+ "Next == Addx \n"
				+ "========================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 * 3 = 7 \n" + "END";
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) * 3 = 9 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (1 + 2) * 3 = 9 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) + 3 = 6 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 + 3 = 6 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testPrecedence4() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 + 3) = 6 \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + (2 + 3) = 6 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

}
