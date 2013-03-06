/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import org.junit.Test;

import de.tla2b.util.Util;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.*;

public class LogicOperatorsTest {


	/**********************************************************************
	 * equality and disequality: =, #,
	 **********************************************************************/
	@Test
	public void testEquality() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (k2 # 1)\n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : BOOL & k2 : INTEGER & k = bool(k2 /= 1)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testEquality2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = TRUE\n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : BOOL & k = TRUE \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testEquality3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE\n" + "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
	 **********************************************************************/
	@Test
	public void testAnd() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (FALSE \\land k2) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : BOOL & k2 : BOOL & k = bool(FALSE = TRUE & k2 = TRUE) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testAnd2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE /\\ (TRUE \\/ FALSE) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE or FALSE = TRUE) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Negation: ~, \neg, \lnot
	 **********************************************************************/
	@Test
	public void testNegation() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\lnot TRUE \n" + "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES not(TRUE = TRUE) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Implication and Equivalence: =>, \equiv
	 **********************************************************************/

	@Test
	public void testImplication() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE /\\ (TRUE => FALSE) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE => FALSE = TRUE) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testEquivalence() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE /\\ (TRUE <=> FALSE) \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE <=> FALSE = TRUE) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Quantification: \A x \in S : P or \E x \in S : P
	 **********************************************************************/
	@Test
	public void testUniversalQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\A x,y \\in {1,2} : x = 0 \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES !x,y.(x : {1, 2} & y : {1, 2} => x = 0) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testExistentialQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\E x,y \\in {1,2} : x = 0 \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES #x,y.(x : {1, 2} & y : {1, 2} & x = 0) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals, Sequences \n"
				+ "CONSTANTS S \n"
				+ "ASSUME S = {1,2,3} /\\  \\E u \\in Seq(S) : \\A s \\in S : \\E n \\in 1..Len(u) : u[n] = s \n"
				+ "=================================";

		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS S\n"
				+ "PROPERTIES S : POW(INTEGER) & S = {1, 2, 3} & #u.(u : seq(S) & !s.(s : S => #n.(n : 1 .. size(u) & u(n) = s))) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	

}
