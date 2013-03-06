/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.*;
import org.junit.Test;

import de.tla2b.util.Util;


public class TestInstanceLet {

	@Test
	public void testInstance() throws Exception {
		String path = "src/test/resources/prettyprint/instance/let/";
		StringBuilder sb = Util.translate(path + "InstanceLet.tla");
		String expected = fileToString(path + "InstanceLet.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
