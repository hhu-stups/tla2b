/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;
import org.junit.Test;
import translation.Main;
import util.ToolIO;

public class TestFunction {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Function constructor
	 **********************************************************************/

	@Test
	public void testFunctionConstructor() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x \\in {1} |-> TRUE = TRUE] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER*BOOL) & k = %x.(x : {1}| bool(TRUE = TRUE)) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFunctionConstructor2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x,y \\in {1} |-> 1] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER*INTEGER*INTEGER) & k = %x,y.(x : {1} & y : {1}| 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFunctionConstructor3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER*BOOL*INTEGER) & k = %x,y.(x : {1} & y : BOOL| 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * recursive Function
	 **********************************************************************/

	@Test
	public void testRecursiveFunction() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "fact[n \\in {1,2}] == IF n = 0 THEN 1 ELSE n+ fact[n-1] \n"
				+ "ASSUME k = fact /\\ fact[k2] = k3 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k,k2,k3\n"
				+ "PROPERTIES k : POW(INTEGER*INTEGER) & k2 : INTEGER & k3 : INTEGER \n"
				+ " & k = fact & fact(k2) = k3 \n"
				+ "DEFINITIONS IF_THEN_ELSE(P, a, b) == (%t_.(t_=0 & P = TRUE | a )\\/%t_.(t_=0 & not(P= TRUE) | b ))(0); \n"
				+ "fact == %n.(n : {1, 2}| IF_THEN_ELSE(bool(n = 0), 1, n + fact(n - 1))) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * Function call
	 **********************************************************************/
	@Test
	public void testFunctionCall() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x,y \\in {1} |-> x+y] /\\ k[1,2] = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + "k : POW(INTEGER*INTEGER*INTEGER)"
				+ "& k = %x,y.(x : {1} & y : {1}| x + y) & k(1, 2) = 1" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFunctionCall2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x \\in {1} |-> TRUE] /\\ k[1] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + "k : POW(INTEGER*BOOL)"
				+ "& k = %x.(x : {1}| TRUE) & k(1) = TRUE\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/***********************************************************************
	 * Domain of Function
	 ***********************************************************************/
	@Test
	public void testDomain() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [x \\in {1} |-> x] /\\ DOMAIN k = {1} \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + "k : POW(INTEGER*INTEGER)"
				+ "& k = %x.(x : {1}| x) & dom(k) = {1}" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Set of Function
	 **********************************************************************/
	@Test
	public void testSetofFunction() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [BOOLEAN -> {1}] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + "k : POW(POW(BOOL*INTEGER))"
				+ "& k = BOOL --> {1}" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Except
	 **********************************************************************/
	@Test
	public void testFunctionExcept() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT ![TRUE] = 0, ![FALSE] = 0]  \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + " k : POW(BOOL*INTEGER)"
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Record Except @
	 **********************************************************************/
	@Test
	public void testFunctionExceptAt() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x \\in {1,2} |-> x] /\\ k2 = [k EXCEPT ![1] = @ + 1] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : POW(INTEGER*INTEGER) &  k2 : POW(INTEGER*INTEGER) & k = %x.(x : {1, 2}| x) & k2 = k <+ {1 |-> k(1) + 1} \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFunctionExceptAt2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x,y \\in {1,2} |-> x+y] /\\ k2 = [k EXCEPT ![1,1] = @ + 4] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES  k : POW(INTEGER*INTEGER*INTEGER) &  k2 : POW(INTEGER*INTEGER*INTEGER) & k = %x,y.(x : {1, 2} & y : {1, 2}| x + y) & k2 = k <+ {(1, 1) |-> k(1, 1) + 4} \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
