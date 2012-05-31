/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestExcept {

	@BeforeClass
	public static void beforeClass() {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Before
	public void before() {
		ToolIO.reset();
	}

	@Test
	public void testRecord() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x|->1,y|->TRUE], b |-> 1] \n"
				+ "/\\ r2 = [r EXCEPT !.a.x = 2] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ "r : struct(a:struct(x:INTEGER,y:BOOL),b:INTEGER) \n"
				+ "& r2 : struct(a:struct(x:INTEGER,y:BOOL),b:INTEGER) \n"
				+ "& r = rec(a : rec(x : 1,y : TRUE),b : 1) & r2 = rec(a : rec(x:2, y:r'a'y), b : r'b) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecord2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x|-> [u|->1]]] \n"
				+ "/\\ r2 = [r EXCEPT !.a.x.u = 2] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:struct(x:struct(u:INTEGER))) \n"
				+ "& r2 : struct(a:struct(x:struct(u:INTEGER))) \n"
				+ "& r = rec(a : rec(x : rec(u : 1))) & r2 = rec(a : rec(x : rec(u : 2))) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunctionRecord() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2,3} |-> [a |-> x] ] \n"
				+ "/\\ r2 = [r EXCEPT ![1].a = 11] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES \n"
				+ " r : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r2 : POW(INTEGER*struct(a:INTEGER)) \n"
				+ "& r = %x.(x : {1, 2, 3}| rec(a : x)) & r2 = r <+ {1 |-> rec(a : 11)} \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testRecordFunction() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> [x \\in {1,2,3} |-> x], b |-> 1 ] \n"
				+ "/\\ r2 = [r EXCEPT !.a[2+1] = 11] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : struct(a:POW(INTEGER*INTEGER),b:INTEGER) \n"
				+ "& r2 : struct(a:POW(INTEGER*INTEGER),b:INTEGER) \n"
				+ "& r = rec(a : %x.(x : {1, 2, 3}| x),b : 1) & r2 = rec(a : (r'a <+ {2 + 1 |-> 11}), b : r'b) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testFunction3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x,y \\in {1,2,3} |-> x+y] \n"
				+ "/\\ r2 = [r EXCEPT ![1,1] = 11] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*INTEGER*INTEGER) \n"
				+ "& r2 : POW(INTEGER*INTEGER*INTEGER) \n"
				+ "& r = %x,y.(x : {1, 2, 3} & y : {1, 2, 3}| x + y) & r2 = r <+ {(1, 1) |-> 11} \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testFunctionFunction() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a \\in {3,4} |-> [b \\in {7,8} |-> a + b]] \n"
				+ "/\\ r2 = [r EXCEPT ![3][7] = 55] \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS r, r2 \n"
				+ "PROPERTIES "
				+ " r : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r2 : POW(INTEGER*POW(INTEGER*INTEGER)) \n"
				+ "& r = %a.(a : {3, 4}| %b.(b : {7, 8}| a + b)) & r2 = r <+ {3 |-> (r(3) <+ {7 |-> 55})} \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
