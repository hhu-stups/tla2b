/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb.standardmodules;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestModuleSequences {

	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	/**********************************************************************
	 * SubSeq(s,m,n)
	 **********************************************************************/
	@Test
	public void testSetEnumeration() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME SubSeq(<<1,2,3,4,5,6>>, 2, 4) = <<2,3,4>> \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES ([1, 2, 3, 4, 5, 6]/|\\4)\\|/2-1 = [2, 3, 4] \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	//TODO test other operators of module sequences
}
