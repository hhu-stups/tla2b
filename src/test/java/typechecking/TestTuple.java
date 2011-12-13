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

public class TestTuple {

	@Test  
	public void testUnifyTuple() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<TRUE>> \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
	}
	
	
	
	@Test  
	public void testUnifyTuple2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = <<k2, k3>> /\\ k3 = TRUE \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}

	@Test  
	public void testUnifyTuple3() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = <<k2, <<k3>> >> /\\ k3 = TRUE \n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*POW(INTEGER*BOOL))", t.constants.get("k").toString());
		assertEquals("POW(INTEGER*BOOL)", t.constants.get("k2").toString());
		assertEquals("BOOL", t.constants.get("k3").toString());
	}
	
	@Test  
	public void testUnifyTuple4() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k \\in <<TRUE>>\n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER*BOOL", t.constants.get("k").toString());
	}
	
	@Test  
	public void testUnifyTuple5() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = <<1,2,3,4,k2>>\n"
				+ "=================================";
	
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(INTEGER*INTEGER)", t.constants.get("k").toString());
		assertEquals("INTEGER", t.constants.get("k2").toString());
	}
	
	
	/**********************************************************************
	 * Cartesian Product
	 **********************************************************************/
	@Test
	public void testCartesianProduct() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X {1} \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL*INTEGER)", t.constants.get("k").toString());
	}
	
	@Test
	public void testCartesianProduct2() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME BOOLEAN \\X {1} = k \\X k2 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("POW(BOOL)", t.constants.get("k").toString());
		assertEquals("POW(INTEGER)", t.constants.get("k2").toString());
	}
	
	@Test (expected = TypeErrorException.class)
	public void testCartesianProductException() throws FrontEndException, MyException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X 1 \n"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
	}
	
}
