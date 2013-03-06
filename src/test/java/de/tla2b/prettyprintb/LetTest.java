/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.*;
import org.junit.Test;

import de.tla2b.util.Util;


public class LetTest {

	@Test
	public void testLetinAssume() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ " bazz == 2\n"
				+ "ASSUME LET foo(a) == k = a + bazz  IN foo(1) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		getTreeAsString(sb.toString());
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES  k : INTEGER & foo(1) \n"
				+ "DEFINITIONS bazz == 2; foo(a) == k = a + bazz \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testLetinDefinition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ " bar(x) == LET foo(a) == x = a IN foo(1) \n"
				+ "ASSUME bar(5) \n" + "=================================";
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "PROPERTIES bar(5) \n"
				+ "DEFINITIONS  foo(a, x) == x = a; bar(x) == foo(1, x) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testLetInNext() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES x\n"
				+ "Init == x = 1\n"
				+ "Next == LET foo(a) == a \n"
				+ "		IN x' = foo(2) \\/ x' = foo(3) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS foo(a) == a \n"
				+ "VARIABLES x \n"
				+ "INVARIANT x:INTEGER\n"
				+ "INITIALISATION x:(x=1)\n"
				+ "OPERATIONS Next1_Op = ANY x_n WHERE x_n : INTEGER & x_n = foo(2)	THEN x := x_n END;\n"
				+ "Next2_Op = ANY x_n WHERE x_n : INTEGER & x_n = foo(3) THEN x := x_n END\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testLetInOperation() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x\n"
				+ "Init == x = 1\n"
				+ "bar == x = 1 /\\ LET val == 1 IN x' = val + val\n"
				+ "bazz == x = 2 /\\ LET val2 == 1 IN x' = val2 * val2\n"
				+ "Next == bar \\/ bazz \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS val == 1; val2 == 1 \n"
				+ "VARIABLES x INVARIANT x : INTEGER INITIALISATION x:(x = 1)\n"
				+ "OPERATIONS bar_Op = ANY x_n WHERE x_n : INTEGER & x = 1 & x_n = val + val THEN x := x_n END; \n"
				+ "bazz_Op = ANY x_n WHERE x_n : INTEGER & x = 2 & x_n = val2 * val2 THEN x := x_n END\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	

	
	@Test
	public void testLetInQuantification() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in {1,2}: LET d == x+1 IN d > x \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES  !x.(x : {1, 2} => d > x) \n"
				+ "DEFINITIONS d == x + 1 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
