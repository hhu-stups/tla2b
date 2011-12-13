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

public class TestMiscellaneousConstructs {

	/**********************************************************************
	 * IF THEN ELSE
	 **********************************************************************/
	@Test
	public void testIfThenElse() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = (IF k2 THEN k3 ELSE k4) /\\ k4 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
		assertEquals("INTEGER", t.constants.get("k4").toString());
	}
	

	/**********************************************************************
	 * IF THEN ELSE
	 **********************************************************************/
	@Test
	public void testCase() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, e1, e2 \n"
				+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2) /\\ e2 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
		assertEquals("INTEGER", t.constants.get("e1").toString());
		assertEquals("INTEGER", t.constants.get("e2").toString());
	}
	
	@Test
	public void testCase2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, e1, e2, e3 \n"
				+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2 [] OTHER -> e3) /\\ e2 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
		assertEquals("INTEGER", t.constants.get("e1").toString());
		assertEquals("INTEGER", t.constants.get("e2").toString());
		assertEquals("INTEGER", t.constants.get("e3").toString());
	}
	
	/**********************************************************************
	 * LET d == exp IN e
	 **********************************************************************/
	@Test
	public void testLetIn() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (LET d == k2 IN d = k3) /\\ k2 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	@Test
	public void testLetIn2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (LET d == k2 d2 == k3 IN d = d2) /\\ k2 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	@Test
	public void testLetIn3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = (LET d(a,b) == a=k2/\\b=k3 IN d(1,k4)) /\\ k4 = TRUE  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
		assertEquals("BOOL", t.constants.get("k4").toString());
	}
	
	
}
