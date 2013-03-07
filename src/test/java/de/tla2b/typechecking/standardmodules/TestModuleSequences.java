/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class TestModuleSequences {

	/**********************************************************************
	 * Seq(S): The set of all sequences of elements in S.
	 **********************************************************************/
	@Test  
	public void testSeq() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Seq({TRUE}) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(POW(INTEGER*BOOL))", t.getConstantType("k"));
	}
	
	@Test  
	public void testSeq2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME <<k>> \\in Seq({TRUE}) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}
	
	
	
	@Test (expected = TypeErrorException.class)
	public void testSeqException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME 1 = Seq({1}) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test (expected = TypeErrorException.class)
	public void testSeqException2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Seq(1) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	/**********************************************************************
	 * Len(S)
	 **********************************************************************/
	@Test  
	public void testLen() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Len(<<1,2,3>>) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLenException() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME TRUE = Len(<<1,2,3>>) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLenException2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME 3 = Len({1,2,3}) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorLen2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = Len(1) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	/**********************************************************************
	 * s \o s2 - concatenation of s and s2
	 **********************************************************************/
	@Test  
	public void testUnifyConcatenation() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = k2 \\o <<TRUE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}
	
	@Test  
	public void testUnifyConcatenation2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME <<TRUE>> = k \\o k2 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}
	
	@Test  
	public void testUnifyConcatenation3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k= k2 \\o k3 /\\ k3 = <<TRUE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k3"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME k = 1 \\o k2 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME 1 = k \\o k2 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME <<TRUE>> = <<1>> \\o <<2>> \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	/**********************************************************************
	 * Append(s, e)
	 **********************************************************************/
	@Test  
	public void testUnifyAppend() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(k2, k3) /\\ k3 = TRUE \n"
				+ "=================================";
	
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}
	
	@Test  
	public void testUnifyAppend2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(k2, k3) /\\ k = <<TRUE>> \n"
				+ "=================================";
	
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}
	
	@Test  
	public void testUnifyAppend3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Append(k2, 1) \n"
				+ "=================================";
	
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k2"));
	}

	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorAppend() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(1, k3) \n"
				+ "=================================";
	
		TestUtil.typeCheckString(module);
	}
	

	/**********************************************************************
	 * Head(s): the first element of the seq
	 **********************************************************************/
	@Test  
	public void testUnifyHead() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Head(k2) /\\ k2 = <<1>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k2"));
	}
	
	@Test  
	public void testUnifyHead2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Head(k2) /\\ k = 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k2"));
	}
	
	@Test (expected = TypeErrorException.class) 
	public void testUnifyErrorHead() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Head(1) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	/**********************************************************************
	 * Tail(s): the sequence without the first element
	 **********************************************************************/
	@Test  
	public void testUnifyTail() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Tail(k2) /\\ k = <<TRUE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}
	
	@Test  
	public void testUnifyTail2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Tail(k2) /\\ k2 = <<TRUE>> \n"
				+ "=================================";
	
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
	}
	
	@Test (expected = TypeErrorException.class)  
	public void testUnifyErrorTail() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Tail(1) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	/**********************************************************************
	 * SubSeq(s,m,n): The sequence <<s[m], s[m+1], ... , s[n]>>
	 **********************************************************************/
	@Test  
	public void testUnifySubSeq() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(k2, m, n) /\\ k = <<TRUE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("m"));
		assertEquals("INTEGER", t.getConstantType("n"));
	}
	
	@Test  
	public void testUnifySubSeq2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(k2, m, n) /\\ k2= <<TRUE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("m"));
		assertEquals("INTEGER", t.getConstantType("n"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorSubSeq() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(1, m, n) \n"
				+ "=================================";
	
		TestUtil.typeCheckString(module);
	}
}
