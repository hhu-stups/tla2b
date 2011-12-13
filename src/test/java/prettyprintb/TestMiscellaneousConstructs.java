/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestMiscellaneousConstructs {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	@Test
	public void testIfThenElse() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = IF 1 = 1 THEN 1 ELSE 2 \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER & k = (%t_.( t_ = 0 & 1 = 1 | 1 )\\/%t_.( t_ = 0 & not(1 = 1) | 2 ))(0) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testIfThenElse2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = IF 1 = 1 THEN TRUE ELSE FALSE \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : BOOL & k = bool( (1 = 1 => TRUE = TRUE) & (not(1=1) => FALSE = TRUE )) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCase() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CASE 1 = 1 -> 1 [] 2 = 1 -> 2 [] 0 = 1 -> 3  \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = (%t_.(t_ = 0 & 1 = 1 | 1) \\/ %t_.(t_ = 0 & 2 = 1 | 2) \\/ %t_.(t_ = 0 & 0 = 1 | 3))(0) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCase2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CASE 1 = 1 \\/ 5 = 6 -> 1 [] 2 = 1  -> 2 [] OTHER -> 3  \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = (%t_.(t_ = 0 & (1 = 1 or 5 = 6) | 1) \\/ %t_.(t_ = 0 & 2 = 1 | 2) \\/ %t_.(t_ = 0 & not(1 = 1 or 5 = 6 or 2 = 1) | 3))(0) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
