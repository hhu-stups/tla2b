/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.MyException;

public class TestDefinitions {

	/**********************************************************************
	 * Definition: foo(a,b) == e
	 **********************************************************************/
	@Test  
	public void testDefinition() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "Next(a,b) ==  a = 1 /\\ b = TRUE  \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("Next").getType().toString());
		assertEquals("INTEGER", t.definitions.get("Next").parameters.get("a").toString());
		assertEquals("BOOL", t.definitions.get("Next").parameters.get("b").toString());
		
	}
	
	@Test  
	public void testDefinition2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(a,b) ==  a = k /\\ b = k2 \n"
				+ "bar == k = 1 /\\ k2 = TRUE \n"
				+ "ASSUME foo(1,FALSE) /\\ bar \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("foo").getType().toString());
		assertEquals("INTEGER", t.definitions.get("foo").parameters.get("a").toString());
		assertEquals("BOOL", t.definitions.get("foo").parameters.get("b").toString());
		assertEquals("BOOL", t.definitions.get("bar").getType().toString());
		
	}
	
	@Test  
	public void testDefinition3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "foo ==  k \n"
				+ "bar == foo = 1 \n"
				+ "ASSUME bar \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.definitions.get("foo").getType().toString());
		assertEquals("BOOL", t.definitions.get("bar").getType().toString());
		
	}
	
	@Test  
	public void testDefinition4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(var, value) ==  var = value \n"
				+ "ASSUME foo(k,1) /\\ foo(k2,TRUE)  \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("foo").getType().toString());
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}
	
	
	
	
	
	/**********************************************************************
	 * Definition Call
	 **********************************************************************/

	@Test  
	public void testDefinitionCall() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo(a) ==  TRUE \n"
				+ "bar == foo(1) \n"
				+ "ASSUME bar \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("foo").getType().toString());
		assertEquals("BOOL", t.definitions.get("bar").getType().toString());
	}
	
	
	@Test  
	public void testDefinitionCall2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo(a) ==  a \n"
				+ "bar == foo(1) \n"
				+ "baz == foo(TRUE) \n"
				+ "ASSUME baz /\\ bar = bar"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("UNTYPED", t.definitions.get("foo").getType().toString());
		assertEquals("INTEGER", t.definitions.get("bar").getType().toString());
		assertEquals("BOOL", t.definitions.get("baz").getType().toString());
	}
	
	
	@Test  
	public void testDefinitionCall3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(a) ==  a \n"
				+ "bar == foo(1) \n"
				+ "baz == k = foo(k2) /\\ k2 = bar  \n"
				+ "ASSUME baz \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("UNTYPED", t.definitions.get("foo").getType().toString());
		assertEquals("INTEGER", t.definitions.get("bar").getType().toString());
		assertEquals("BOOL", t.definitions.get("baz").getType().toString());
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	
	@Test  
	public void testDefinitionCall4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(a,b) ==  a \\cup b \n"
				+ "bar == foo({1}, k) \n"
				+ "baz == foo({TRUE}, k2)\n"
				+ "ASSUME baz = baz /\\ bar = bar"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(UNTYPED)", t.definitions.get("foo").getType().toString());
		assertEquals("POW(INTEGER)", t.definitions.get("bar").getType().toString());
		assertEquals("POW(BOOL)", t.definitions.get("baz").getType().toString());
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
		assertEquals("POW(BOOL)", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testDefinitionCall5() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "foo(a,b) ==  a = b \n"
				+ "bar == foo(1,k) \n"
				+ "ASSUME bar \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("foo").getType().toString());
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
	@Test  
	public void testDefinitionCall6() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(a,b) ==  a = b \n"
				+ "bar == foo(k, k2) /\\ k2 = 1 \n"
				+ "ASSUME bar \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.definitions.get("foo").getType().toString());
		assertEquals("UNTYPED", t.definitions.get("foo").parameters.get("a").toString());
		assertEquals("UNTYPED", t.definitions.get("foo").parameters.get("b").toString());
		assertEquals("BOOL", t.definitions.get("bar").getType().toString());
		
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test  
	public void testDefinitionCall7() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "foo(a,b) ==  a \\cup b \n"
				+ "bar(x,y) == x = foo(y, k) /\\ y ={1} \n"
				+ "ASSUME bar(k2,k3) \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(UNTYPED)", t.definitions.get("foo").getType().toString());
		assertEquals("POW(UNTYPED)", t.definitions.get("foo").parameters.get("a").toString());
		assertEquals("POW(UNTYPED)", t.definitions.get("foo").parameters.get("b").toString());
		assertEquals("BOOL", t.definitions.get("bar").getType().toString());
		assertEquals("POW(INTEGER)", t.definitions.get("bar").parameters.get("x").toString());
		assertEquals("POW(INTEGER)", t.definitions.get("bar").parameters.get("y").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	
	@Test  
	public void testDefinitionCall8() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "foo(a) ==  k = a \n"
				+ "bar == foo(k2)\n"
				+ "baz == k2 = 1 \n"
				+ "ASSUME bar /\\ baz \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		System.out.println(t.definitions.get("foo").parameters.get("a"));
	}
}
