/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;

public class TestExcept {

	
	/**********************************************************************
	 * Simple
	 **********************************************************************/
	
	@Test
	public void testFunctionExcept() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![TRUE] = 0]  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL*INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(BOOL*INTEGER)", t.constants.get("k2").toString());
	}
	
	@Ignore
	@Test
	public void testRecordRecord() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k2 = [k EXCEPT ![1].a = 2, ![1].b = k3 ] /\\ k3 = 2 \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		System.out.println(t.constants.get("k").toString());
//		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
//		assertEquals("INTEGER", t.constants.get("k2").toString());
//		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}
	
	@Test
	public void testRecordRecord2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k2 = [k EXCEPT ![1].a = 2, ![1].b = k3 ] /\\ k3 = TRUE \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		System.out.println(t.constants.get("k").toString());
//		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
//		assertEquals("INTEGER", t.constants.get("k2").toString());
//		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}
	
	@Test
	public void testRecord() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT !.a = 2, !.b = TRUE] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
	}
	@Ignore
	@Test
	public void testRecord2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k EXCEPT !.a = 2, !.b = k2] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		System.out.println( t.constants.get("k").toString());
		//assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
	}
	
}
