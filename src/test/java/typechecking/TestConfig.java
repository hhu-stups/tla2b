/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;

public class TestConfig {

	@Test
	public void TestConAssignment() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "=================================";
		final String config = "CONSTANTS k = 1";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	

	@Test
	public void TestConOverride() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo == 1\n"
				+ "ASSUME k2 = k\n"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	// TODO DefOverriding
	
}
