/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.TestUtil;


public class TestInstanceConstantSubstitution {

	private static String path = "src/test/resources/prettyprint/instance/constantSubstitution/";

	@Test
	public void TestExp4Con() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "InstanceValue.tla");
		final String expected = "MACHINE InstanceValue\n"
				+ "ABSTRACT_CONSTANTS c \n" + "PROPERTIES c : INTEGER & def \n"
				+ "DEFINITIONS def == c = 1 + 1 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestCon4Con() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "InstanceValue2.tla");
		final String expected = "MACHINE InstanceValue2\n"
				+ "ABSTRACT_CONSTANTS c, val2 \n"
				+ "PROPERTIES c : INTEGER & val2 : INTEGER & def & val2 = 1 \n"
				+ "DEFINITIONS def == c = val2 \n" + "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestDef4OpArg() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "InstanceOpArg2.tla");
		final String expected = "MACHINE InstanceOpArg2 \n"
				+ "ABSTRACT_CONSTANTS c2 \n"
				+ "PROPERTIES c2 : INTEGER & def & c2 = 3 \n"
				+ "DEFINITIONS bar(a,b) == a + b; def == c2 = bar(1, 2)\n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test (expected = ConfigFileErrorException.class)
	public void TestOpArg4OpArgException() throws Exception {
		TestUtil.translate(path + "InstanceOpArgException.tla");
	}

	@Test
	public void TestOpArg4OpArg() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "InstanceOpArg3.tla", "InstanceOpArg3.cfg");
		final String expected = "MACHINE InstanceOpArg3 \n"
				+ "ABSTRACT_CONSTANTS c2 \n"
				+ "PROPERTIES c2 : INTEGER & def & c2 = 3 \n"
				+ "DEFINITIONS bazz(a,b) == a + b; def == c2 = bazz(1, 2)\n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestInstanced2Times() throws Exception {
		StringBuilder sb = TestUtil.translate(path + "InstanceInstanceOpArg.tla", "InstanceInstanceOpArg.cfg");
		final String expected = "MACHINE InstanceInstanceOpArg \n"
				+ "ABSTRACT_CONSTANTS c3 \n"
				+ "PROPERTIES c3 : INTEGER & def & c3 = 3 \n"
				+ "DEFINITIONS bazz(a,b) == a + b; def == c3 = bazz(1, 2)\n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

}
