/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestLet {

	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testLet() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ " bazz == 2\n"
				+ "ASSUME LET foo(a) == k = a + bazz  IN foo(1) \n"
				+ " bar(x) == LET foo(a) == x = a IN foo(1) \n"
				+ "ASSUME bar(5) /\\ k = 1 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		getTreeAsString(sb.toString());
//		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
//				+ "PROPERTIES k : INTEGER  & foo(1) \n"
//				+ "DEFINITIONS foo(a) == k = a \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testLetInNext() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES x\n"
				+ "Init == x = 1\n"
				+ "Next == LET foo(a) == a \n"
				+ "		IN x' = foo(2) \\/ x' = foo(3) \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		getTreeAsString(sb.toString());
//		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
//				+ "PROPERTIES k : INTEGER  & foo(1) \n"
//				+ "DEFINITIONS foo(a) == k = a \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testLetInOperation() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "VARIABLES x\n"
				+ "Init == x = 1\n"
				+ "bar == x = 1 /\\ LET val == 1 IN x' = val + val\n"
				+ "bazz == x = 2 /\\ LET val == 1 IN x' = val * val\n"
				+ "Next == bar \\/ bazz \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		getTreeAsString(sb.toString());
		//System.out.println(sb);
//		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
//				+ "PROPERTIES k : INTEGER  & foo(1) \n"
//				+ "DEFINITIONS foo(a) == k = a \n" + "END";
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	
}
