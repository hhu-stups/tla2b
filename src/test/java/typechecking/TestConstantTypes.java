/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import exceptions.FrontEndException;
import exceptions.MyException;
import exceptions.TypeErrorException;

import util.ToolIO;
import util.TypeCheckerTest;

public class TestConstantTypes {

	@Test
	public void test1() throws FrontEndException, MyException {

		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = 1 /\\ k2 = k\n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test
	public void test2() throws FrontEndException, MyException {

		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = k2 /\\ k = 1\n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test
	public void test3() throws FrontEndException, MyException {

		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 /\\ k = k3 /\\ k3 = 1\n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
		assertEquals("INTEGER", t.constants.get("k3").toString());
	}


	
	@Test
	public void worstCaseUnification() throws FrontEndException, MyException{
		ToolIO.setMode(ToolIO.TOOL);
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
		
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("a").toString());
		assertEquals("INTEGER", t.constants.get("b").toString());
		assertEquals("INTEGER", t.constants.get("c").toString());
		assertEquals("INTEGER", t.constants.get("d").toString());
		assertEquals("INTEGER", t.constants.get("e").toString());
		assertEquals("INTEGER", t.constants.get("f").toString());
		assertEquals("INTEGER", t.constants.get("g").toString());
		assertEquals("INTEGER", t.constants.get("h").toString());
	}
	
	

	

	
	@Test (expected = TypeErrorException.class) 
	public void prime() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "Next ==  1' = 1 \n"
				+ "=================================";
		
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	@Test (expected = TypeErrorException.class) 
	public void prime2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo ==  k' = 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	@Test 
	public void ifThenElse() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = IF 1 = 1 THEN k2 ELSE 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	
	
	
}
