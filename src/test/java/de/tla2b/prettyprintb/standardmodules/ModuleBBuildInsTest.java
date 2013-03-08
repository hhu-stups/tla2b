package de.tla2b.prettyprintb.standardmodules;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;

public class ModuleBBuildInsTest {

	
	@Test
	public void testPow1() throws Exception {
		String path = "src/test/resources/prettyprint/BBuildIns/";
		StringBuilder sb = TestUtil.translate(path + "Pow1.tla");
		final String expected = "MACHINE Pow1\n"
				+ "PROPERTIES {{1}} = POW1({1}) \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
