/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;
import org.junit.Test;

import de.tla2b.util.Util;

public class ExtendTest {

	@Test
	public void testExtendConAssign() throws Exception {
		String path = "src/test/resources/prettyprint/extends/";
		StringBuilder sb = Util.translate(path + "ExtendsCounter.tla", "ExtendsCounter.cfg");
		String expected = fileToString(path + "ExtendsCounter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testExtendModConAssign() throws Exception {
		String path = "src/test/resources/prettyprint/extends/";
		StringBuilder sb = Util.translate(path + "ExtendsCounter.tla", "ExtendsCounter2.cfg");
		String expected = fileToString(path + "ExtendsCounter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}