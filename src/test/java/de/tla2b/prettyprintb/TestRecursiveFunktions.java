/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import org.junit.Test;

import de.tla2b.translation.Translator;
import de.tla2b.util.Util;

import util.ToolIO;

public class TestRecursiveFunktions {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testIfThenElse() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "foo[a \\in Nat] == IF a = 0 THEN 0 ELSE a + foo[a-1]\n"
				+ "ASSUME k[3] = 6 \n"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
//		final String expected = "MACHINE Testing\n"
//				+ "PROPERTIES foo(1, 2) = 3 \n"
//				+ "DEFINITIONS foo(a,b) == a + b \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testIfThenElse2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+"EXTENDS Naturals \n"
				+ "fact[n \\in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1] \n"
				+ "ASSUME fact[0] = 1 /\\ fact[3] = 6 \n"
				+ "=================================";
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
//		final String expected = "MACHINE Testing\n"
//				+ "PROPERTIES foo(1, 2) = 3 \n"
//				+ "DEFINITIONS foo(a,b) == a + b \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
