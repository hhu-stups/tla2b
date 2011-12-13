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
import exceptions.TypeErrorException;

public class TestBBuiltIns {


	/**********************************************************************
	 * BOOLEAN
	 **********************************************************************/
	@Test  
	public void testBoolean() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)  
	public void testBooleanException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 \\in BOOLEAN \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
	}
	

	/**********************************************************************
	 * String
	 **********************************************************************/
	@Test  
	public void testString() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = STRING \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(STRING)", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorString() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME 1 = STRING \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	/**********************************************************************
	 * Bool value: TRUE, FALSE
	 **********************************************************************/
	@Test  
	public void testBoolValue() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = TRUE \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.constants.get("k").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testUnifyErrorBoolValue() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = TRUE \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
	
	
}
