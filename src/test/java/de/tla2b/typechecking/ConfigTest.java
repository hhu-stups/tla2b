/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class ConfigTest {

	@Test
	public void TestConAssignment() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n" + "=================================";
		final String config = "CONSTANTS k = 1";
		TestTypeChecker t = TestUtil.typeCheckString(module, config);
		assertEquals("INTEGER", t.getConstantType("k").toString());
	}

	@Test
	public void TestConOverride() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo == 1\n"
				+ "ASSUME k2 = k\n"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		TestTypeChecker t = TestUtil.typeCheckString(module, config);
		assertEquals("INTEGER", t.getConstantType("k2").toString());
	}

	// TODO DefOverriding

}
