/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

import de.tla2b.util.TestUtil;

public class ExtendTest {

	@Test
	public void testExtendConAssign() throws Exception {
		String path = "src/test/resources/prettyprint/extends/";
		StringBuilder sb = TestUtil.translate(path + "ExtendsCounter.tla", "ExtendsCounter.cfg");
		String expected = TestUtil.fileToString(path + "ExtendsCounter.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testExtendModConAssign() throws Exception {
		String path = "src/test/resources/prettyprint/extends/";
		StringBuilder sb = TestUtil.translate(path + "ExtendsCounter.tla", "ExtendsCounter2.cfg");
		String expected = TestUtil.fileToString(path + "ExtendsCounter.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}