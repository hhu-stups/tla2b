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


public class ExceptTest {

	@Test
	public void testFunction() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k2 EXCEPT ![TRUE] = 0]  \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k"));
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k2"));
	}

	@Test
	public void testFunctionRecord() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k EXCEPT ![1] = [a|-> 1, b |-> TRUE], ![1].b = k2 ] "
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*struct(a:INTEGER,b:BOOL))",
				t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	@Test
	public void testFunctionRecord2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k EXCEPT ![1].a = 2, ![1].b = k2 ] /\\ k2 = TRUE \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*struct(a:INTEGER,b:BOOL))",
				t.getConstantType("k"));
	}

	@Test
	public void testRecord() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT !.a = 2, !.b = TRUE] \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(a:INTEGER,b:BOOL)", t.getConstantType("k")
				.toString());
	}

	@Test (expected = TypeErrorException.class)
	public void testRecordOrFunction() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS a, b \n"
				+ "ASSUME a = [a EXCEPT !.a = 1, !.b = 1] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> TRUE] \n"
				+ "/\\ r2 = [r EXCEPT !.a = 1 = @] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2}|->TRUE] \n"
				+ "/\\ r2 = [r EXCEPT ![1] = 1 = @] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2}|->TRUE] \n"
				+ "/\\ r2 = [r EXCEPT ![1] = @ + 1] \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [k EXCEPT ![1] = @ = @] \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

}
