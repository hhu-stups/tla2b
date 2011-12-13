/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;
import exceptions.TypeErrorException;

public class TestStruct {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	/**********************************************************************
	 * Set of Records: [L1 : e1, L2 : e2]
	 **********************************************************************/
	@Test  
	public void testStruct() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(struct(a:INTEGER,b:BOOL))", t.constants.get("k").toString());
	}
	
	@Test  
	public void testStruct2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a : k2, b : k3] /\\ k2 = {1} /\\ k3 = BOOLEAN \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(struct(a:INTEGER,b:BOOL))", t.constants.get("k").toString());
	}
	
	@Test  
	public void testStruct3() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [a : {1}, b : BOOLEAN] = [a : k, b : k2] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(BOOL)", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)  
	public void testStructException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = [a : 1, b : TRUE] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testStructException2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a : {1}, b : BOOLEAN] = [a : BOOLEAN, b : BOOLEAN] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testStructException3() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [aa : {1}, b : BOOLEAN] = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	

	/**********************************************************************
	 *Record: [L1 |-> e1, L2 |-> e2]
	 **********************************************************************/
	
	@Test  
	public void testRecord() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
	}
	
	@Test  
	public void testRecord2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a |-> k2, b |-> k3] /\\ k2 = 1 /\\ k3 = TRUE \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRecordException() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	@Test 
	public void testRecord3() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME [a |-> k, b |-> k2] \\in [a: {1}, b: BOOLEAN]  \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}
	
	/**********************************************************************
	 *Record Select: r.c
	 **********************************************************************/
	
	@Test  
	public void testRecordSelect() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = k.a \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testRecordSelect2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k2 = k.a /\\ k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testRecordSelect3() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a |-> k2, b |-> k3]  /\\ k.a = 1 /\\ k.b = TRUE \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test  
	public void testRecordSelect4() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k \\in [a : k2, b : k3]  /\\ k.a = 1 /\\ k.b = TRUE \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
		assertEquals("POW(BOOL)", t.constants.get("k3").toString());
	}
	
	
	@Test (expected = TypeErrorException.class)
	public void testRecordSelectException() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME TRUE = k.a  /\\ k = [a |-> 1] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRecordSelectException2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = k.a /\\ TRUE = k.b  /\\ k = [a |-> 1] \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRecordSelectException3() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ TRUE = k.b \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRecordSelectException4() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ TRUE = k.a \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 *Record Except
	 **********************************************************************/
	
	@Test  
	public void testRecordExcept() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3, k4 \n"
				+ "ASSUME k = [a|-> k2, b|-> k3] /\\ k4 = [k EXCEPT !.a = 1, !.b = TRUE]\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k4").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test  
	public void testRecordExcept2() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k.a = 1/\\ k2 = [k EXCEPT !.a = 1, !.b = TRUE] /\\ k2 = [a|->2, b |-> FALSE]\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k").toString());
		assertEquals("struct(a:INTEGER,b:BOOL)", t.constants.get("k2").toString());
	}
	
	/**********************************************************************
	 *Record Except @
	 **********************************************************************/
	
	@Test  
	public void testRecordExceptAt() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a|-> TRUE] /\\ k2 = [k EXCEPT !.a = @ = k3]\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("struct(a:BOOL)", t.constants.get("k").toString());
		assertEquals("struct(a:BOOL)", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testRecordExceptAtException() throws FrontEndException, MyException {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = [a|-> TRUE] /\\ k2 = [k EXCEPT !.a = @ = 1]\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
}
