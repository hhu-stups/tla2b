package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class TupleTest {

	@Test
	public void testSimpleTuple() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<1,TRUE>> \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k").toString());
	}

	@Test
	public void testTuple3Components() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<1,TRUE,1>> \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL*INTEGER", t.getConstantType("k").toString());
	}
	
	@Test
	public void testTuple3Components2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<1,1,1>> \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*INTEGER*INTEGER", t.getConstantType("k").toString());
	}

	@Test
	public void testTupleComponentsOfTheSameType() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<1,1>> \n" + "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*INTEGER", t.getConstantType("k").toString());
	}

	@Test
	public void testTuple1() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = <<1,k2>> /\\ k2 = TRUE \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k").toString());
		assertEquals("BOOL", t.getConstantType("k2").toString());
	}

	@Test
	public void testCartesianProduct() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = {1} \\times BOOLEAN \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k").toString());
	}

	@Test
	public void testTupleSingleElement() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<TRUE>> \n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testTuple2Elements() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = <<k2, k3>> /\\ k3 = TRUE \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}

	@Test
	public void testUnifyTuple3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = <<k2, <<k3>> >> /\\ k3 = TRUE /\\ k2 = 1\n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*POW(INTEGER*BOOL)", t.getConstantType("k")
				.toString());
		assertEquals("INTEGER", t.getConstantType("k2").toString());
		assertEquals("BOOL", t.getConstantType("k3").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testUnifyTuple4() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k \\in <<TRUE>>\n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}

	/**********************************************************************
	 * Cartesian Product
	 **********************************************************************/
	@Test
	public void testCartesianProduct2() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X {1} \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k").toString());
	}

	@Test
	public void testCartesianProduct3() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME BOOLEAN \\X {1} = k \\X k2 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k").toString());
		assertEquals("POW(INTEGER)", t.getConstantType("k2").toString());
	}

	@Test(expected = TypeErrorException.class)
	public void testCartesianProductException() throws FrontEndException,
			TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X 1 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
