/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class FunctionTest {

	/**********************************************************************
	 * Function constructor
	 **********************************************************************/

	@Test
	public void testSimpleFunctionConstructor() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x \\in {1} |-> 1] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testFunctionConstructor() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S \n"
				+ "ASSUME k = [x \\in S |-> x = k2] /\\ k2 = 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
	}

	@Test
	public void testFunctionConstructorTwoVariables() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x,y \\in {1} |-> TRUE]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER*BOOL)", t.getConstantType("k")
				.toString());
	}

	@Test
	public void testFunctionConstructor2() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [<<x,y>> \\in {<<1,TRUE>>} |-> TRUE]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*BOOL)", t.getConstantType("k")
				.toString());
	}

	@Test
	public void testFunctionConstructor6() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x \\in {1}, <<y,z>> \\in {<<1,TRUE>>} |-> TRUE]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		//System.out.println(t.getConstantType("k").toString());
		assertEquals("POW(INTEGER*(INTEGER*BOOL)*BOOL)", t.getConstantType("k")
				.toString());
	}

	@Test
	public void testFunctionConstructorTwoVariables2()
			throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> TRUE]  \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*BOOL)", t.getConstantType("k")
				.toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testFunctionConstructorFail() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [<<x,y>> \\in {1}  |-> TRUE]  \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test (expected = TypeErrorException.class)
	public void testFunctionConstructorFail2() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [<<x,y,z>> \\in ({1} \\times {1}) |-> TRUE]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		System.out.println(t.getConstantType("k"));
	}

	@Test
	public void testFunctionConstructor3() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, S, S2 \n"
				+ "ASSUME k = [x,y \\in S, z \\in S2 |-> z] /\\ S = BOOLEAN /\\ S2 = {1}  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*BOOL*INTEGER*INTEGER)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("S"));
		assertEquals("POW(INTEGER)", t.getConstantType("S2"));
	}

	@Test
	public void testFunctionConstructor4() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S, S2 \n"
				+ "ASSUME [x \\in S |-> k] = [x \\in S2 |-> x=k2] /\\ k2 = 1  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
		assertEquals("POW(INTEGER)", t.getConstantType("S2"));
	}

	@Test
	public void testFunctionConstructor5() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME [x \\in S, y \\in S2 |-> 1] = [x,y \\in {1} |-> 1]   \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
		assertEquals("POW(INTEGER)", t.getConstantType("S2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testFunctionConstructorException() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S, S2 \n"
				+ "ASSUME [x \\in S, y \\in S2 |-> 1] = [x \\in {1} |-> 1]   \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * recursive Function
	 **********************************************************************/
	@Test
	public void testRecursiveFunction() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "fact[n \\in {1,2}] == IF n = 0 THEN 1 ELSE n+ fact[n-1] \n"
				+ "ASSUME k = fact /\\ fact[k2] = k3 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	/**********************************************************************
	 * Function call
	 **********************************************************************/

	@Test
	public void testFunctionCall() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[1] = TRUE \n" + "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testFunctionCall2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[1,TRUE,2] = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testFunctionCall3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, S \n"
				+ "ASSUME k[k2,TRUE] = k3 \n"
				+ "ASSUME k = [x \\in {1}, y \\in S |-> 1]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
		assertEquals("POW(BOOL)", t.getConstantType("S"));
	}

	@Test
	public void testFunctionCall4() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k[(TRUE /\\ TRUE)] = 2 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testFunctionCallException() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, S \n"
				+ "ASSUME k = [x \\in {1} |-> 1]\n"
				+ "ASSUME k[k2,TRUE] = k3 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Domain
	 **********************************************************************/
	@Test
	public void testDomain() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]\n"
				+ "ASSUME k2 = DOMAIN k \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}

	@Test
	public void testDomain2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]\n"
				+ "ASSUME k2 = DOMAIN k \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}

	/**********************************************************************
	 * Set of Function
	 **********************************************************************/
	@Test
	public void testSetOfFunction() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [BOOLEAN -> {1}] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(POW(BOOL*INTEGER))", t.getConstantType("k"));
	}

	@Test
	public void testSetOfFunction2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME [x \\in BOOLEAN |-> 1] \\in [S -> S2] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("S"));
		assertEquals("POW(INTEGER)", t.getConstantType("S2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfFunctionException() throws FrontEndException,
			TLA2BException {
		/*
		 * A set of tuple is not a function in TLA+
		 */
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S, S2 \n"
				+ "ASSUME {1} \\X BOOLEAN \\in [S -> S2] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Except
	 **********************************************************************/
	@Test
	public void testFunctionExcept() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![TRUE] = 0]  \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);

		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k"));
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k2"));
	}

	@Test
	public void testFunctionExcept2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [k2 EXCEPT ![TRUE,1] = k3] /\\ k3 = 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*INTEGER*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("POW(BOOL*INTEGER*INTEGER)", t.getConstantType("k2")
				.toString());
		assertEquals("INTEGER", t.getConstantType("k3"));

	}

	@Test
	public void testFunctionExcept3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4, k5 \n"
				+ "ASSUME k = [k2 EXCEPT ![k3,k4] = k5]\n"
				+ "ASSUME k2 = [x \\in {1}, y \\in BOOLEAN |-> 1]"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k2")
				.toString());
		assertEquals("INTEGER", t.getConstantType("k3"));
		assertEquals("BOOL", t.getConstantType("k4"));
		assertEquals("INTEGER", t.getConstantType("k5"));

	}

	@Test
	public void testFunctionExcept4() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4, k5 \n"
				+ "ASSUME k = [k2 EXCEPT ![k3,k4] = k5]\n"
				+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1]"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k")
				.toString());
		assertEquals("POW(INTEGER*BOOL*INTEGER)", t.getConstantType("k2")
				.toString());
		assertEquals("INTEGER", t.getConstantType("k3"));
		assertEquals("BOOL", t.getConstantType("k4"));
		assertEquals("INTEGER", t.getConstantType("k5"));
	}

	@Test
	public void testFunctionExcept6() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4\n"
				+ "ASSUME k = [k2 EXCEPT ![k3] = k4, ![1] = TRUE ]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2").toString());
		assertEquals("INTEGER", t.getConstantType("k3"));
		assertEquals("BOOL", t.getConstantType("k4"));
	}

	@Test
	public void testFunctionExcept5() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![1][1] = 2]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*POW(INTEGER*INTEGER))",
				t.getConstantType("k"));
		assertEquals("POW(INTEGER*POW(INTEGER*INTEGER))",
				t.getConstantType("k2"));
	}

	@Test
	public void testFunctionExcept7() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![<<1,2>>] = 2]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER*INTEGER)", t.getConstantType("k"));
	}

	/**********************************************************************
	 * Except @
	 **********************************************************************/

	@Test
	public void testAt2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2,k3 \n"
				+ "ASSUME k = [k2 EXCEPT ![1] = TRUE, ![2] = @=k3]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testAtException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![1] = TRUE, ![2] = @=1]  \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
