/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb.standardmodules;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

import de.tla2b.util.TestUtil;

public class ModuleTLA2BTest {

	@Test
	public void testMinOfSet() throws Exception {
		String path = "src/test/resources/prettyprint/standardModules/";
		StringBuilder sb = TestUtil.translate(path + "MinOfSet.tla");
		final String expected = "MACHINE MinOfSet\n"
				+ "PROPERTIES min({1, 2, 3}) = 1 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testSetProduct() throws Exception {
		String path = "src/test/resources/prettyprint/standardModules/";
		StringBuilder sb = TestUtil.translate(path + "SetProduct.tla");
		final String expected = "MACHINE SetProduct\n"
				+ "PROPERTIES PI(z_).(z_:{1, 2, 3}|z_) = 6 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testSetSummation() throws Exception {
		String path = "src/test/resources/prettyprint/standardModules/";
		StringBuilder sb = TestUtil.translate(path + "SetSummation.tla");
		final String expected = "MACHINE SetSummation\n"
				+ "PROPERTIES SIGMA(z_).(z_:{1, 2, 3}|z_) = 6 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testPerm() throws Exception {
		String path = "src/test/resources/prettyprint/standardModules/";
		StringBuilder sb = TestUtil.translate(path + "PermutedSequences.tla");
		final String expected = "MACHINE PermutedSequences\n"
				+ "PROPERTIES perm({1, 2}) = {[1, 2], [2, 1]} \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
}
