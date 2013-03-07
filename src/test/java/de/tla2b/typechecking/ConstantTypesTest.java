/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class ConstantTypesTest {

	@Test
	public void test1() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = 1 /\\ k2 = k\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void test2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = k2 /\\ k = 1\n"
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void test3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 /\\ k = k3 /\\ k3 = 1\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test
	public void worstCaseUnification() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c, d, e, f, g, h \n"
				+ "ASSUME a = b \n"
				+ "ASSUME c = d \n"
				+ "ASSUME a = c \n"
				+ "ASSUME e = f \n"
				+ "ASSUME g = h \n"
				+ "ASSUME e = g \n"
				+ "ASSUME a = e \n"
				+ "ASSUME h = 1 \n" 
				+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("a"));
		assertEquals("INTEGER", t.getConstantType("b"));
		assertEquals("INTEGER", t.getConstantType("c"));
		assertEquals("INTEGER", t.getConstantType("d"));
		assertEquals("INTEGER", t.getConstantType("e"));
		assertEquals("INTEGER", t.getConstantType("f"));
		assertEquals("INTEGER", t.getConstantType("g"));
		assertEquals("INTEGER", t.getConstantType("h"));
	}

	@Test(expected = TypeErrorException.class)
	public void prime() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "Next ==  1' = 1 \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void prime2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo ==  k' = 1 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void ifThenElse() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = IF 1 = 1 THEN k2 ELSE 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

}
