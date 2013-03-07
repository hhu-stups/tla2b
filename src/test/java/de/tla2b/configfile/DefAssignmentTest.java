/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.configfile;

import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.util.TestUtil;


public class DefAssignmentTest {
	
	@Test 
	public void testIntegerAssigned() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = 1 \n"
				+ "=================================";
		final String config = "CONSTANTS foo = 1";
		StringBuilder sb = TestUtil.translateString(module, config);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES foo = 1 \n"
				+ "DEFINITIONS foo == 1 \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
	@Ignore
	@Test 
	public void testModelvalueAssigned() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = foo \n"
				+ "=================================";
		final String config = "CONSTANTS foo = a";
		StringBuilder sb = TestUtil.translateString(module, config);
		System.out.println(sb);
		String expected = "MACHINE Testing \n"
				+ "SETS ENUM1 = {a} \n"
				+ "PROPERTIES foo = foo \n"
				+ "DEFINITIONS foo == a \n"
				+ "END";
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Ignore
	@Test 
	public void testModelvalueAssignedSameName() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo == 5 \n"
				+ "ASSUME foo = foo \n"
				+ "=================================";
		final String config = "CONSTANTS foo = foo";
		StringBuilder sb = TestUtil.translateString(module);
		System.out.println(sb);
		String expected = "MACHINE Testing \n"
				+ "PROPERTIES foo = foo \n"
				+ "DEFINITIONS foo == 1 \n"
				+ "END";
		assertEquals(TestUtil.getTreeAsString(expected), TestUtil.getTreeAsString(sb.toString()));
	}
	
}
