/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class InstanceTest {

	/**********************************************************************
	 * Instance
	 **********************************************************************/

	@Test
	public void testOneInstanced() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = TestUtil.translate(path + "OneInstanced.tla");
		String expected = TestUtil.fileToString(path + "OneInstanced.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testTwoInstanced() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = TestUtil.translate(path + "TwoInstanced");
		String expected = TestUtil.fileToString(path + "TwoInstanced.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testInstanceNoName() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = TestUtil.translate(path + "InstanceNoName.tla");
		System.out.println(sb);
		String expected = TestUtil.fileToString(path + "InstanceNoName.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestInstanceOpArg() throws Exception {
		String path = "src/test/resources/prettyprint/instance/OpArg/";
		StringBuilder sb = TestUtil.translate(path + "OpArgInstanced.tla");
		String expected = TestUtil.fileToString(path + "OpArgInstanced.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestInstanceDefinition() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = TestUtil.translate(path + "InstanceDefinition.tla");
		String expected = TestUtil.fileToString(path + "InstanceDefinition.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void TestModConstantAssignment() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = TestUtil.translate(path + "ModConstantAssignment.tla", "ModConstantAssignment.cfg");
		String expected = TestUtil.fileToString(path + "ModConstantAssignment.mch");
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

}
