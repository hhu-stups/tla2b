/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class TestUnchanged {

	private static String path = "src/test/resources/prettyprint/unchanged/";

	@Test
	public void testOneUnchangedVariable() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "OneUnchangedVariable.tla");
		String expected = TestUtil.fileToString(path + "OneUnchangedVariable.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testSeveralUnchangedVariables() throws Exception {
		StringBuilder sb = TestUtil
				.translate(path + "SeveralUnchangedVariables.tla");
		String expected = TestUtil.fileToString(path + "SeveralUnchangedVariables.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

}
