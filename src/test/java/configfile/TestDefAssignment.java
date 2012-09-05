/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Ignore;
import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestDefAssignment {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	@Test 
	public void testIntegerAssigned() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = 1 \n"
				+ "=================================";
		final String config = "CONSTANTS foo = 1";
		StringBuilder sb = Main.start(module, config, true);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES foo = 1 \n"
				+ "DEFINITIONS foo == 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test 
	public void testModelvalueAssigned() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = foo \n"
				+ "=================================";
		final String config = "CONSTANTS foo = a";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		String expected = "MACHINE Testing \n"
				+ "SETS ENUM1 = {a} \n"
				+ "PROPERTIES foo = foo \n"
				+ "DEFINITIONS foo == a \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Ignore
	@Test 
	public void testModelvalueAssignedSameName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = foo \n"
				+ "=================================";
		final String config = "CONSTANTS foo = foo";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES foo = foo \n"
				+ "DEFINITIONS foo == 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
