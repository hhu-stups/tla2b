/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.configfile;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class ConstantOverrideTest {

	@Test
	public void testConstantOverridenByDef() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ " foo == 5 \n"
				+ "ASSUME k = 5"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = TestUtil.translateString(module, config);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo = 5 \n"
				+ "DEFINITIONS foo == 5 \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testConstantOverridenByDef2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_) \n"
				+ " foo(a,b) == a = b \n"
				+ "ASSUME k(1,1) = TRUE"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES bool(foo(1,1)) = TRUE \n"
				+ "DEFINITIONS foo(a, b) == a = b \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
