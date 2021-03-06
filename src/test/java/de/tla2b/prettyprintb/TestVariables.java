/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.translation.Tla2BTranslator;
import de.tla2b.util.TestUtil;

import util.ToolIO;

public class TestVariables {

	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void testSetEnumeration() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "=================================";
		
		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}
