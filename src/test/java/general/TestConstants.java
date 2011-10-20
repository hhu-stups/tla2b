package general;


import org.junit.Test;

import exceptions.TypeErrorException;
import translation.Main;
import util.ToolIO;
import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;


public class TestConstants {
	
	
	@Test(expected = TypeErrorException.class)
	public void TestPrime() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = 1\n"
				+ "foo == k' \n"
				+ "=================================";
		Main.start(module, null, true);
	}
	
	@Test(expected = TypeErrorException.class)
	public void TestPrime2() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo == 1' \n"
				+ "=================================";
		Main.start(module, null, true);
	}
	
	
	
	@Test
	public void TestSetEnumeration() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1,2,3}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & k = {1,2,3}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
