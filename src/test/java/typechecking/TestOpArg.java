/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import exceptions.ConfigFileErrorException;

import util.ToolIO;
import util.TypeCheckerTest;

public class TestOpArg {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	@Test
	public void TestConOverridenByLessOp() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_), k2 \n"
				+ "ASSUME k2 = k(1,2)\n"
				+ "=================================";
		final String config = "CONSTANTS k <- <";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}
	
	@Test (expected = ConfigFileErrorException.class)
	public void TestOverridenConstantWrongArityException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_) \n"
				+ "def == TRUE /\\ FALSE \n"
				+ "=================================";
		final String config = "CONSTANTS k <- def";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
	}
	
	@Test (expected = ConfigFileErrorException.class)
	public void TestOverridenDefWrongArityException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo(a, b) == a /\\ b  \n"
				+ "def == TRUE /\\ FALSE \n"
				+ "ASSUME foo(TRUE, FALSE) \n"
				+ "=================================";
		final String config = "CONSTANTS foo <- def";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
	}
	
	
	@Test 
	public void TestOverridenByDef() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k(_,_), k2 \n"
				+ "def(a,b) == a /\\ b \n"
				+ "ASSUME k2 = k(TRUE,TRUE)\n"
				+ "=================================";
		final String config = "CONSTANTS k <- def";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}
}
