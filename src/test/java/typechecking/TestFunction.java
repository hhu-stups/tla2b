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
import exceptions.TypeErrorException;

public class TestFunction {

	/**********************************************************************
	 * Function constructor
	 **********************************************************************/

	@Test
	public void testFunctionConstructor() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, S \n"
				+ "ASSUME k = [x \\in S |-> x = k2] /\\ k2 = 1 \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}

	@Test
	public void testFunctionConstructor2() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, S2 \n"
				+ "ASSUME k = [x,y \\in S, z \\in S2 |-> z] /\\ S = BOOLEAN /\\ S2 = {1}  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL*BOOL*INTEGER*INTEGER)", t.constants.get("k")
				.toString());
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S2").toString());
	}

	@Test
	public void testFunctionConstructor3() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S \n"
				+ "ASSUME [x,y \\in {1} |-> TRUE] = [x,y \\in S |-> k]  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}

	@Test
	public void testFunctionConstructor4() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S, S2 \n"
				+ "ASSUME [x \\in S |-> k] = [x \\in S2 |-> x=k2] /\\ k2 = 1  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S2").toString());
	}

	@Test
	public void testFunctionConstructor5() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME [x \\in S, y \\in S2 |-> 1] = [x,y \\in {1} |-> 1]   \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testFunctionConstructorException() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S, S2 \n"
				+ "ASSUME [x \\in S, y \\in S2 |-> 1] = [x \\in {1} |-> 1]   \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * recursive Function
	 **********************************************************************/
	@Test
	public void testRecursiveFunction() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "fact[n \\in {1,2}] == IF n = 0 THEN 1 ELSE n+ fact[n-1] \n"
				+ "ASSUME k = fact /\\ fact[k2] = k3 \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}
	
	/**********************************************************************
	 * Function call
	 **********************************************************************/

	@Test
	public void testFunctionCall() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[1] = TRUE \n" + "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}

	@Test
	public void testFunctionCall2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[1,TRUE,2] = TRUE \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER*BOOL)", t.constants.get("k")
				.toString());
	}

	@Test
	public void testFunctionCall3() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, S \n"
				+ "ASSUME k[k2,TRUE] = k3 \n"
				+ "ASSUME k = [x \\in {1}, y \\in S |-> 1]\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k")
				.toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
	}
	
	@Test
	public void testFunctionCall4() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[(TRUE /\\ TRUE)] = 2 \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL*INTEGER)", t.constants.get("k")
				.toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testFunctionCallException() throws FrontEndException,
			TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, S \n"
				+ "ASSUME k = [x \\in {1} |-> 1]\n"
				+ "ASSUME k[k2,TRUE] = k3 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();

	}

	/**********************************************************************
	 * Domain
	 **********************************************************************/
	@Test
	public void testDomain() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]\n"
				+ "ASSUME k2 = DOMAIN k \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}

	@Test
	public void testDomain2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]\n"
				+ "ASSUME k2 = DOMAIN k \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}
	
	

	/**********************************************************************
	 * Set of Function
	 **********************************************************************/
	@Test
	public void testSetOfFunction() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [BOOLEAN -> {1}] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(POW(BOOL*INTEGER))", t.constants.get("k").toString());
	}

	@Test
	public void testSetOfFunction2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME [x \\in BOOLEAN |-> 1] \\in [S -> S2] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S2").toString());
	}
	
	
	@Test
	public void testSetOfFunction3() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME {1} \\X BOOLEAN \\in [S -> S2] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
		assertEquals("POW(BOOL)", t.constants.get("S2").toString());
	}
	
	/**********************************************************************
	 * Except
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
	
	@Test
	public void testFunctionExcept2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [k2 EXCEPT ![TRUE,1] = k3] /\\ k3 = 1 \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL*INTEGER*INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(BOOL*INTEGER*INTEGER)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
		
	}
	
	@Test
	public void testFunctionExcept3() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4, k5 \n"
				+ "ASSUME k = [k2 EXCEPT ![k3,k4] = k5]\n"
				+ "ASSUME k2 = [x \\in {1}, y \\in BOOLEAN |-> 1]"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
		assertEquals("BOOL", t.constants.get("k4").toString());
		assertEquals("INTEGER", t.constants.get("k5").toString());
		
	}
	
	@Test
	public void testFunctionExcept4() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4, k5 \n"
				+ "ASSUME k = [k2 EXCEPT ![k3,k4] = k5]\n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
		assertEquals("BOOL", t.constants.get("k4").toString());
		assertEquals("INTEGER", t.constants.get("k5").toString());
	}
	
	@Test
	public void testFunctionExceptException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![1][1] = 2]\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*POW(INTEGER*INTEGER))", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*POW(INTEGER*INTEGER))", t.constants.get("k2").toString());
	}
	@Test
	public void testFunctionExceptException2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![<<1,2>>] = 2]\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	/**********************************************************************
	 * Except @
	 **********************************************************************/
	
	@Test
	public void testAt2() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2,k3 \n"
				+ "ASSUME k = [k2 EXCEPT ![1] = TRUE, ![2] = @=k3]  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	
	@Test (expected = TypeErrorException.class)
	public void testAtException() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![1] = TRUE, ![2] = @=1]  \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
}
