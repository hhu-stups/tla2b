package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class TupleVsSequenceTest {

	@Test  
	public void testTupleVsSequence() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Append(<<>>, TRUE) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}
	
	@Test  
	public void testTupleVsSequence2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Append(<<1,2,3>>, k2) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}
	
	@Test  
	public void testTupleVsSequence3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a, b, c\n"
				+ "ASSUME <<1,2,3,4>> = <<a,b,c>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("a"));
		assertEquals("INTEGER", t.getConstantType("b"));
		assertEquals("INTEGER", t.getConstantType("c"));
	}
	
}
