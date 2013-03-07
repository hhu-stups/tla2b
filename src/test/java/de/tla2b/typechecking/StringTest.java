/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class StringTest {
	
	/**********************************************************************
	 * a String: "abc"
	 **********************************************************************/

	@Test
	public void testAString() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = \"abc\" \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("STRING", t.getConstantType("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testAStringException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = \"abc\" \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	/**********************************************************************
	 * STRING
	 **********************************************************************/
	@Test 
	public void testString() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = STRING \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(STRING)", t.getConstantType("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testStringException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = STRING \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
}
