/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.translation.Translator;
import de.tla2b.util.Util;

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
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
