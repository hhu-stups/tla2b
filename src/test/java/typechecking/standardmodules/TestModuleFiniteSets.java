/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;
import exceptions.TypeErrorException;

public class TestModuleFiniteSets {

	/**********************************************************************
	 * IsFiniteSet
	 **********************************************************************/
	@Test
	public void unifyIsFiniteSet() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = IsFiniteSet({1,2,3}) \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
	}

	@Test
	public void unifyIsFiniteSet2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = IsFiniteSet(k2) /\\ k2 = {1} \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());

	}

	@Test
	public void unifyIsFiniteSet3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = IsFiniteSet({}) \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorIsFiniteSet() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME IsFiniteSet(1)\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorIsFiniteSet2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME 1 = IsFiniteSet({1})\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * Cardinality
	 **********************************************************************/
	@Test
	public void unifyCardinality() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Cardinality({1,2,3}) \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
	}

	@Test
	public void unifyCardinality2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Cardinality(k2) /\\ k2 = {1} \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorCardinality() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME Cardinality(1)\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorCardinality2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS FiniteSets \n"
				+ "ASSUME TRUE = Cardinality({1})\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

}
