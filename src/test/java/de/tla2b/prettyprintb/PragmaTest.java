package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.ToolIO;
import de.tla2b.util.TestUtil;

public class PragmaTest {

	
	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testPragma() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS (*@unit *) k, k2 \n"
				+ "ASSUME k =1 /\\ k2 = 2 \n"
				+ "VARIABLES (*@unit *) x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "=================================";
		
		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : INTEGER  & k2 : INTEGER & k = 1 & k2 = 2 \n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
