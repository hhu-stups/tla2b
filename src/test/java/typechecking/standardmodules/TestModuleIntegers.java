/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking.standardmodules;

import static org.junit.Assert.*;

import org.junit.Test;

import util.ToolIO;
import util.TypeCheckerTest;
import exceptions.FrontEndException;
import exceptions.TLA2BException;
import exceptions.TypeErrorException;

public class TestModuleIntegers {


	/**********************************************************************
	 * Int
	 **********************************************************************/
	@Test  
	public void unifyInt() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Int \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void unifyErrorInt() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers \n"
				+ "ASSUME TRUE \\in Int \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * unary minus: -x
	 **********************************************************************/
	@Test  
	public void unifyUnaryMinus() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = -k2 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void unifyErrorUnaryMinus() throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers \n"
				+ "ASSUME TRUE = -1 \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
}
