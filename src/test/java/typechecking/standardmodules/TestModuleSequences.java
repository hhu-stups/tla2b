/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;
import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;
import exceptions.TypeErrorException;

public class TestModuleSequences {

	/**********************************************************************
	 * Seq(S): The set of all sequences of elements in S.
	 **********************************************************************/
	@Test  
	public void testSeq() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Seq({TRUE}) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(POW(INTEGER*BOOL))", t.constants.get("k").toString());
	}
	
	@Test  
	public void testSeq2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME <<k>> \\in Seq({TRUE}) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
	}
	
	
	
	@Test (expected = TypeErrorException.class)
	public void testSeqException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME 1 = Seq({1}) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}

	@Test (expected = TypeErrorException.class)
	public void testSeqException2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Seq(1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	/**********************************************************************
	 * Len(S)
	 **********************************************************************/
	@Test  
	public void testLen() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Len({1,2,3}) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLenException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME TRUE = Len({1,2,3}) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorLen2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = Len(1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	/**********************************************************************
	 * s \o s2 - concatenation of s and s2
	 **********************************************************************/
	@Test  
	public void testUnifyConcatenation() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = k2 \\o <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testUnifyConcatenation2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME <<TRUE>> = k \\o k2 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testUnifyConcatenation3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k= k2 \\o k3 /\\ k3 = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME k = 1 \\o k2 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME 1 = k \\o k2 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorConcatenation3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2  \n"
				+ "ASSUME <<TRUE>> = <<1>> \\o <<2>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	/**********************************************************************
	 * Append(s, e)
	 **********************************************************************/
	@Test  
	public void testUnifyAppend() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(k2, k3) /\\ k3 = TRUE \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test  
	public void testUnifyAppend2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(k2, k3) /\\ k = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test  
	public void testUnifyAppend3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Append(k2, 1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k2").toString());
	}

	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorAppend() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = Append(1, k3) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	

	/**********************************************************************
	 * Head(s): the first element of the seq
	 **********************************************************************/
	@Test  
	public void testUnifyHead() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Head(k2) /\\ k2 = <<1>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testUnifyHead2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Head(k2) /\\ k = 1 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class) 
	public void testUnifyErrorHead() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Head(1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * Tail(s): the sequence without the first element
	 **********************************************************************/
	@Test  
	public void testUnifyTail() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Tail(k2) /\\ k = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testUnifyTail2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = Tail(k2) /\\ k2 = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)  
	public void testUnifyErrorTail() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Tail(1) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * SubSeq(s,m,n): The sequence <<s[m], s[m+1], ... , s[n]>>
	 **********************************************************************/
	@Test  
	public void testUnifySubSeq() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(k2, m, n) /\\ k = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("m").toString());
		assertEquals("INTEGER", t.constants.get("n").toString());
	}
	
	@Test  
	public void testUnifySubSeq2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(k2, m, n) /\\ k2= <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("m").toString());
		assertEquals("INTEGER", t.constants.get("n").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorSubSeq() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "CONSTANTS k, k2, m, n \n"
				+ "ASSUME k = SubSeq(1, m, n) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
}
