/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb.standardmodules;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestModuleTLA2B {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	
	/**********************************************************************
	 * MinOfSet
	 **********************************************************************/
	@Test
	public void testMinOfSet() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "MinOfSet(a) == 1 \n"
				+ "ASSUME MinOfSet({1,2,3}) = 1 \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES min({1, 2, 3}) = 1 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	/**********************************************************************
	 * SetProduct
	 **********************************************************************/
	@Test
	public void testSetProduct() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "SetProduct(a) == {} \n"
				+ "ASSUME SetProduct({1,2,3}) = 6 \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES PI(z_).(z_:{1, 2, 3}|z_) = 6 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * SetSummation
	 **********************************************************************/
	@Test
	public void testSetSummation() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "SetSummation(a) == {} \n"
				+ "ASSUME SetSummation({1,2,3}) = 6 \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES SIGMA(z_).(z_:{1, 2, 3}|z_) = 6 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
