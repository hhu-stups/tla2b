/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.Util;

public class ConstantWithArgsTest {

	@Test
	public void TestInstanceOpSubstitution() throws Exception {
		String path = "src/test/resources/prettyprint/constantWithArgs/";
		StringBuilder sb = Util.translate(path + "InstanceCounter.tla");
		String expected = fileToString(path + "InstanceCounter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test (expected= ConfigFileErrorException.class)
	public void TestOpArgNotOverridenException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS c(_) \n"
				+ "ASSUME c(1) = 2 \n"
				+ "=================================";
		Util.translateString(module);
	}
	
}
