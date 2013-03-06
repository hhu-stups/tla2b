/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.*;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;


public class InstanceTest {

	/**********************************************************************
	 * Instance
	 **********************************************************************/

	@Test
	public void testOneInstanced() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = Util.translate(path + "OneInstanced.tla");
		String expected = fileToString(path + "OneInstanced.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testTwoInstanced() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = Util.translate(path + "TwoInstanced");
		String expected = fileToString(path + "TwoInstanced.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testInstanceNoName() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = Util.translate(path + "InstanceNoName.tla");
		System.out.println(sb);
		String expected = fileToString(path + "InstanceNoName.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestInstanceOpArg() throws Exception {
		String path = "src/test/resources/prettyprint/instance/OpArg/";
		StringBuilder sb = Util.translate(path + "OpArgInstanced.tla");
		String expected = fileToString(path + "OpArgInstanced.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestInstanceDefinition() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = Util.translate(path + "InstanceDefinition.tla");
		String expected = fileToString(path + "InstanceDefinition.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestModConstantAssignment() throws Exception {
		String path = "src/test/resources/prettyprint/instance/Counter/";
		StringBuilder sb = Util.translate(path + "ModConstantAssignment.tla", "ModConstantAssignment.cfg");
		String expected = fileToString(path + "ModConstantAssignment.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
