/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestStruct {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Set of Records: [L1 : e1, L2 : e2]
	 **********************************************************************/
	@Test
	public void testStruct() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(struct(a:INTEGER,b:BOOL)) & k = struct(a : {1}, b : BOOL) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testStructExpansion() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a: {2}] = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES struct(a : {2},b : BOOL) = struct(a : {1},b : BOOL) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Record: [L1 |-> e1, L2 |-> e2]
	 **********************************************************************/
	@Test
	public void testRecord() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : struct(a:INTEGER,b:BOOL) & k = rec(a : 1, b : TRUE) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testRecordExpansion() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a|-> 2] = [a |-> 1, b |-> \"abc\"] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES rec(a : 2,b : \"\") = rec(a : 1,b : \"abc\") \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Record Select: r.c
	 **********************************************************************/
	@Test
	public void testRecordSelect() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = k.a \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES  k : struct(a:INTEGER,b:BOOL) &  k2 : INTEGER & k = rec(a : 1, b : TRUE) & k2 = k'a \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecordSelect2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k.b \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES  k : struct(a:INTEGER,b:BOOL) &  k = rec(a : 1, b : TRUE) & k'b = TRUE \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Record Except
	 **********************************************************************/
	@Test
	public void testRecordExcept() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = [k EXCEPT !.a = 2] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES  k : struct(a:INTEGER,b:BOOL) &  k2 : struct(a:INTEGER,b:BOOL) & k = rec(a : 1, b : TRUE) & k2 = rec(a : 2, b : k'b) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * Record Except @
	 **********************************************************************/
	@Test
	public void testRecordExceptAt() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = [k EXCEPT !.a = @ + 1] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : struct(a:INTEGER,b:BOOL) &  k2 : struct(a:INTEGER,b:BOOL) & k = rec(a : 1, b : TRUE) & k2 = rec(a : k'a + 1, b : k'b) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
