/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb.standardmodules;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.Util;


public class TestModuleSequences {

	
	/**********************************************************************
	 * SubSeq(s,m,n)
	 **********************************************************************/
	@Test
	public void testSetEnumeration() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME SubSeq(<<1,2,3,4,5,6>>, 2, 4) = <<2,3,4>> \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES ([1, 2, 3, 4, 5, 6]/|\\4)\\|/2-1 = [2, 3, 4] \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	//TODO test other operators of module sequences
}
