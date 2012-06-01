/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;
import exceptions.TypeErrorException;

public class TestExcept {

	@Before
	public void beforeTest() {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
	}

	@Test
	public void testFunction() throws FrontEndException, TLA2BException {
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
	public void testFunctionRecord() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k EXCEPT ![1] = [a|-> 1, b |-> TRUE], ![1].b = k2 ] "
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*struct(a:INTEGER,b:BOOL))",
				t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}

	@Test
	public void testFunctionRecord2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [k EXCEPT ![1].a = 2, ![1].b = k2 ] /\\ k2 = TRUE \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*struct(a:INTEGER,b:BOOL))",
				t.constants.get("k").toString());
	}

	@Test
	public void testRecord() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT !.a = 2, !.b = TRUE] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k")
				.toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordOrFunction() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS a, b \n"
				+ "ASSUME a = [a EXCEPT !.a = 1, !.b = 1] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [a |-> TRUE] \n"
				+ "/\\ r2 = [r EXCEPT !.a = 1 = @] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2}|->TRUE] \n"
				+ "/\\ r2 = [r EXCEPT ![1] = 1 = @] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test(expected = TypeErrorException.class)
	public void testRecordAtTypeError3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS r, r2\n"
				+ "ASSUME  r = [x \\in {1,2}|->TRUE] \n"
				+ "/\\ r2 = [r EXCEPT ![1] = @ + 1] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test
	public void testRecordAtTypeError4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = [k EXCEPT ![1] = @ = @] \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}

}
