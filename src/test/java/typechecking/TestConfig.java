/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;

public class TestConfig {

	@Test
	public void TestConAssignment() throws FrontEndException, MyException {
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
	public void TestConOverride() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "foo == 1"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
	@Test // TODO DefOverriding
	public void TestConOverride2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "foo == 1"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
}
