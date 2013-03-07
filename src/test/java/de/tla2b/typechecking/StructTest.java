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

import util.ToolIO;

public class StructTest {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Set of Records: [L1 : e1, L2 : e2]
	 **********************************************************************/
	@Test
	public void testStruct() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(struct(a:INTEGER,b:BOOL))", t.getConstantType("k"));
	}

	@Test
	public void testStruct2() throws FrontEndException, TLA2BException {

		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a : k2, b : k3] /\\ k2 = {1} /\\ k3 = BOOLEAN \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		
		assertEquals("POW(struct(a:INTEGER,b:BOOL))", t.getConstantType("k"));
	}

	@Test
	public void testStruct3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [a : {1}, b : BOOLEAN] = [a : k, b : k2] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testStructException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = [a : 1, b : TRUE] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testStructException2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a : {1}, b : BOOLEAN] = [a : BOOLEAN, b : BOOLEAN] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testStructException3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [aa : {1}, b : BOOLEAN] = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Record: [L1 |-> e1, L2 |-> e2]
	 **********************************************************************/

	@Test
	public void testRecord() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testRecord2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a |-> k2, b |-> k3] /\\ k2 = 1 /\\ k3 = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = [b |-> 1, a |-> TRUE] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testRecord3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [a |-> k, b |-> k2] \\in [a: {1}, b: BOOLEAN]  \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	/**********************************************************************
	 * Record Select: r.c
	 **********************************************************************/

	@Test
	public void testRecordSelect() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = k.a \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testRecordSelect2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k2 = k.a /\\ k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testRecordSelect3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a |-> k2, b |-> k3]  /\\ k.a = 1 /\\ k.b = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test
	public void testRecordSelect4() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k \\in [a : k2, b : k3]  /\\ k.a = 1 /\\ k.b = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
		assertEquals("POW(BOOL)", t.getConstantType("k3"));
	}

	@Test
	public void testRecordSelectException3() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ TRUE = k.b \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testRecordSelect5() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = k.a /\\ TRUE = k.b  /\\ k = [a |-> 1] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordSelectException() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME TRUE = k.a  /\\ k = [a |-> 1] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordSelectException4() throws FrontEndException,
			TLA2BException {

		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ TRUE = k.a \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Record Except
	 **********************************************************************/

	@Test
	public void testRecordExcept() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = [a|-> k2, b|-> k3] /\\ k4 = [k EXCEPT !.a = 1, !.b = TRUE]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k4"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test
	public void testRecordExcept2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k.a = 1/\\ k2 = [k EXCEPT !.a = 1, !.b = TRUE] /\\ k2 = [a|->2, b |-> FALSE]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k"));
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k2"));
	}

	/**********************************************************************
	 * Record Except @
	 **********************************************************************/

	@Test
	public void testRecordExceptAt() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a|-> TRUE] /\\ k2 = [k EXCEPT !.a = @ = k3]\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:BOOL)", t.getConstantType("k"));
		assertEquals("struct(a:BOOL)", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordExceptAtException() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a|-> TRUE] /\\ k2 = [k EXCEPT !.a = @ = 1]\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
}
