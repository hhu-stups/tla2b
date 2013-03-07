/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.util.TestUtil;

import util.ToolIO;

public class ChooseTest {

	
	@Test
	public void testChoose() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = CHOOSE x \\in {1,2,3}: TRUE \n"
				+ "=================================";

		StringBuilder sb = TestUtil.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = CHOOSE({x|x : {1, 2, 3} & TRUE = TRUE}) \n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T);"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

}
