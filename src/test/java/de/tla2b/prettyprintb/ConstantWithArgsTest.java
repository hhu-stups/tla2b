/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.TestUtil;

public class ConstantWithArgsTest {

	@Test
	public void TestInstanceOpSubstitution() throws Exception {
		String path = "src/test/resources/prettyprint/constantWithArgs/";
		StringBuilder sb = TestUtil.translate(path + "InstanceCounter.tla");
		String expected = TestUtil.fileToString(path + "InstanceCounter.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test (expected= ConfigFileErrorException.class)
	public void TestOpArgNotOverridenException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS c(_) \n"
				+ "ASSUME c(1) = 2 \n"
				+ "=================================";
		TestUtil.translateString(module);
	}
	
}
