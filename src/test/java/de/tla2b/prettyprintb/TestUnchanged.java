/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;


public class TestUnchanged {

	private static String path = "src/test/resources/prettyprint/unchanged/";

	@Test
	public void testOneUnchangedVariable() throws Exception {
		StringBuilder sb = Util.translate(path + "OneUnchangedVariable.tla");
		String expected = fileToString(path + "OneUnchangedVariable.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testSeveralUnchangedVariables() throws Exception {
		StringBuilder sb = Util
				.translate(path + "SeveralUnchangedVariables.tla");
		String expected = fileToString(path + "SeveralUnchangedVariables.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
