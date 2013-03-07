/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class ExceptTest {

	@Test
	public void testRecord() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x|->1,y|->TRUE], b |-> 1] \n"
				+ "/\\ r2 = [r EXCEPT !.a.x = 2] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ "r : struct(a:struct(x:INTEGER,y:BOOL),b:INTEGER) \n"
				+ "& r2 : struct(a:struct(x:INTEGER,y:BOOL),b:INTEGER) \n"
				+ "& r = rec(a : rec(x : 1,y : TRUE),b : 1) & r2 = rec(a : rec(x:2, y:r'a'y), b : r'b) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecord2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x|-> [u|->1]]] \n"
				+ "/\\ r2 = [r EXCEPT !.a.x.u = 2] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:struct(x:struct(u:INTEGER))) \n"
				+ "& r2 : struct(a:struct(x:struct(u:INTEGER))) \n"
				+ "& r = rec(a : rec(x : rec(u : 1))) & r2 = rec(a : rec(x : rec(u : 2))) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunctionRecord() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2,3} |-> [a |-> x] ] \n"
				+ "/\\ r2 = [r EXCEPT ![1].a = 11] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES \n"
				+ " r : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r2 : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r = %x.(x : {1, 2, 3}| rec(a : x)) & r2 = r <+ {1 |-> rec(a : 11)} \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testRecordFunction() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x \\in {1,2,3} |-> x], b |-> 1 ] \n"
				+ "/\\ r2 = [r EXCEPT !.a[2+1] = 11] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:POW(INTEGER*INTEGER),b:INTEGER) \n"
				+ "& r2 : struct(a:POW(INTEGER*INTEGER),b:INTEGER) \n"
				+ "& r = rec(a : %x.(x : {1, 2, 3}| x),b : 1) & r2 = rec(a : (r'a <+ {2 + 1 |-> 11}), b : r'b) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunction3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x,y \\in {1,2,3} |-> x+y] \n"
				+ "/\\ r2 = [r EXCEPT ![1,1] = 11] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*INTEGER*INTEGER) \n"
				+ "& r2 : POW(INTEGER*INTEGER*INTEGER) \n"
				+ "& r = %x,y.(x : {1, 2, 3} & y : {1, 2, 3}| x + y) & r2 = r <+ {(1, 1) |-> 11} \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testFunctionFunction() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a \\in {3,4} |-> [b \\in {7,8} |-> a + b]] \n"
				+ "/\\ r2 = [r EXCEPT ![3][7] = 55] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r2 : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r = %a.(a : {3, 4}| %b.(b : {7, 8}| a + b)) & r2 = r <+ {3 |-> (r(3) <+ {7 |-> 55})} \n"
				+ "END";
		System.out.println(TestUtil.getTreeAsString(sb.toString()));
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecordDualFieldAccess() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> 1] \n"
				+ "/\\ r2 = [r EXCEPT !.a = 3, !.a = 4] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:INTEGER) \n"
				+ "& r2 : struct(a:INTEGER) \n"
				+ "& r = rec(a : 1) & r2 = rec(a : 4) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecordRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [b|-> 1]] \n"
				+ "/\\ r2 = [r EXCEPT !.a.b = @] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:struct(b:INTEGER)) \n"
				+ "& r2 : struct(a:struct(b:INTEGER)) \n"
				+ "& r = rec(a : rec(b : 1)) & r2 = rec(a : rec(b : r'a'b)) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunctionFunctionAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1}|-> [y \\in {1} |-> x + y]] \n"
				+ "/\\ r2 = [r EXCEPT ![1][1] = @ + 1] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r2 : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r = %x.(x : {1}| %y.(y : {1}| x + y)) & r2 = r <+ {1 |-> (r(1) <+ {1 |-> r(1)(1) + 1})} \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecordFunctionAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a|-> [x \\in {1} |-> x]] \n"
				+ "/\\ r2 = [r EXCEPT !.a[1] = @ + 1] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:POW(INTEGER*INTEGER)) \n"
				+ "& r2 : struct(a:POW(INTEGER*INTEGER)) \n"
				+ "& r = rec(a : %x.(x : {1}| x)) & r2 = rec(a : (r'a <+ {1 |-> r'a(1) + 1})) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunctionRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1} |-> [a|-> x]] \n"
				+ "/\\ r2 = [r EXCEPT ![1].a = @ + 1] \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r2 : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r = %x.(x : {1}| rec(a : x)) & r2 = r <+ {1 |-> rec(a : r(1)'a + 1)} \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}
