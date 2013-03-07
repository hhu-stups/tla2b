/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.*;
import org.junit.Test;

import de.tla2b.util.TestUtil;


public class TestInstanceLet {

	@Test
	public void testInstance() throws Exception {
		String path = "src/test/resources/prettyprint/instance/let/";
		StringBuilder sb = TestUtil.translate(path + "InstanceLet.tla");
		String expected = TestUtil.fileToString(path + "InstanceLet.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
