package de.tla2b.configfile;
/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

import static org.junit.Assert.assertEquals;
import org.junit.Test;

import de.tla2b.util.TestUtil;

public class ConstantAssignmentTest {
	
	@Test
	public void testValueAssignedToConstant() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "=================================";
		final String config = "CONSTANTS k = 1";
		StringBuilder sb = TestUtil.translateString(module, config);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k = 1 \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testModelvalueAssignedToConstant() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "=================================";
		final String config = "CONSTANTS k = a";
		StringBuilder sb = TestUtil.translateString(module, config);
		final String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {a}"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k = a \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}

	@Test
	public void testModelvalueAssignedToConstantWithTheSameName() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "=================================";
		final String config = "CONSTANTS k = k";
		StringBuilder sb = TestUtil.translateString(module, config);
		final String expected = "MACHINE Testing\n"
				+ "SETS ENUM1 = {k}"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}
