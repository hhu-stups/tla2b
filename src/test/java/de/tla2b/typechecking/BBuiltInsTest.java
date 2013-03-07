/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class BBuiltInsTest {


	/**********************************************************************
	 * BOOLEAN
	 **********************************************************************/
	@Test  
	public void testBoolean() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)  
	public void testBooleanException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 \\in BOOLEAN \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
	}
	

	/**********************************************************************
	 * String
	 **********************************************************************/
	@Test  
	public void testString() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = STRING \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(STRING)", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorString() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = STRING \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	/**********************************************************************
	 * Bool value: TRUE, FALSE
	 **********************************************************************/
	@Test  
	public void testBoolValue() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorBoolValue() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = TRUE \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	
}
