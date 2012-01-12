/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;
import exceptions.TypeErrorException;

public class TestSet {

	/**********************************************************************
	 * Set Enumeration: {1,2,3}
	 **********************************************************************/

	@Test
	public void testSetEnumeration() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = {k2, k3} /\\ k3 = 1\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());

	}

	@Test
	public void testSetEnumeration2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = {k2, k3} /\\ k = {1}\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test
	public void testSetEnumeration3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = {k2,{k3}} /\\ k3 = 1\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(POW(INTEGER))", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}

	@Test
	public void testSetEnumeration4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = {{1},{k2}}\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(POW(INTEGER))", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSetEnumerationException() throws FrontEndException,
			MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = {1, TRUE}\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testSetEnumerationException2() throws FrontEndException,
			MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME 1 = {1, 2}\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * Element of: \in, \notin
	 **********************************************************************/
	@Test
	public void testElementOfSet() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k \\in {k2} /\\ k2 = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testElementOfSet2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k \\in {k2} /\\ k = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testElementOfSet3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k \\in {<<TRUE>>}\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testElementOfSetError() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = (1 \\in {1}) \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testElementOfSetError2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 \\in 1 \n" + "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * set operators like difference, union, intersection
	 **********************************************************************/
	@Test
	public void testSetOperators() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = (k2 \\cup k3) /\\ k3 = {1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k3").toString());
	}

	@Test
	public void testSetOperators2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (k \\cup k2) /\\ k2 = {1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOperatorsException() throws FrontEndException,
			MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME 1 = k \\cup k2 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOperatorsException2() throws FrontEndException,
			MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1} \\cup {TRUE} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * set constructor: {x \in S : p}.
	 **********************************************************************/
	@Test
	public void testSubsetOf() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME k = {x \\in S : x = 1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}

	@Test
	public void testSubsetOf2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = {x \\in {TRUE} : x = k2} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}

	@Test
	public void testSubsetOf3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, k2\n"
				+ "ASSUME k = {x \\in S : x = k2} /\\ k2 = TRUE \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}

	@Test
	public void testSubsetOf4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME k = {x \\in S : TRUE} /\\ k = {TRUE} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
	}

	@Test (expected = TypeErrorException.class)
	public void testSubsetOfException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {<<x,y>> \\in {TRUE} : TRUE} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetOfException2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {x \\in 1 : TRUE} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetOfException3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {x \\in {} : 1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * set constructor: {e : x \in S}
	 **********************************************************************/
	@Test
	public void testSetOfAll() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, k2\n"
				+ "ASSUME k = {x = k2 : x \\in S} /\\ k2 = 1  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testSetOfAll2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME k = {{x} : x \\in S} /\\ S = {1}  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(POW(INTEGER))", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
	}

	@Test
	public void testSetOfAll3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, k2\n"
				+ "ASSUME k = { x = y /\\ y = k2 : x,y \\in S} /\\ k2 = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("S").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testSetOfAll4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, S2, k2, k3\n"
				+ "ASSUME k = { x = k2 /\\ y /\\ z = k3 : x \\in S, y,z \\in S2 } /\\ k2 = TRUE \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(BOOL)", t.constants.get("S").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfAllException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME 1 = {x : x \\in S} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfAllException2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME k = {x : x \\in 1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test (expected = TypeErrorException.class)
	public void testSetOfAllException3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S\n"
				+ "ASSUME k = {x : <<x,y>> \\in S} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * SUBSET: conforms POW in B
	 **********************************************************************/
	@Test
	public void testSubset() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = SUBSET k2 /\\ k2 = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test
	public void testSubset2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = SUBSET k2 /\\ k = {1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = SUBSET k \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * UNION
	 **********************************************************************/
	@Test
	public void testUnion() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = UNION k2 /\\ k = {1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(POW(INTEGER))", t.constants.get("k2").toString());
	}

	@Test
	public void testUnion2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = UNION k2 /\\ k2 = {{1},{2}} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(POW(INTEGER))", t.constants.get("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testUnionException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = UNION k2 /\\ k = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testUnionException2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = UNION k2 /\\ k2 = {1,2} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	/**********************************************************************
	 * Subseteq: subset or equal
	 **********************************************************************/
	@Test
	public void testSubseteq() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (k2 \\subseteq k3) /\\ k3 = {1}  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k3").toString());
	}

	@Test (expected = TypeErrorException.class)
	public void testSubseteqException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = (k2 \\subseteq 1)  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testSubseteqException2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME 1 = (k \\subseteq k2)  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
}
