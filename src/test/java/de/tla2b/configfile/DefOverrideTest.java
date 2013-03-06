/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.configfile;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;


public class DefOverrideTest {

	@Test 
	public void testDefOverriddenByDef() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo == 1 \n"
				+ "bar == 2 \n"
				+ "ASSUME foo = 2 \n"
				+ "=================================";
		final String config = "CONSTANTS foo <- bar";
		StringBuilder sb = Util.translateString(module, config);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES bar = 2 \n"
				+ "DEFINITIONS bar == 2 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
