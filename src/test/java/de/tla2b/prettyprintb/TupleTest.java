/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;


public class TupleTest {
	
	/**********************************************************************
	 * Tuple
	 **********************************************************************/
	@Test
	public void testTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = <<TRUE,FALSE,TRUE>>\n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : BOOL*BOOL*BOOL & k = (TRUE,FALSE,TRUE) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * Cartesian Product
	 **********************************************************************/
	@Test
	public void testCartesianProduct() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X {1} \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(BOOL*INTEGER) & k = BOOL*{1} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCartesianProduct2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X ({1} \\X BOOLEAN) \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(BOOL*(INTEGER*BOOL)) & k = BOOL*({1}*BOOL) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
}
