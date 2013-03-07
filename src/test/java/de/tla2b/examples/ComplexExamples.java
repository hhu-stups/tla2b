/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.examples;



import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.util.TestUtil;


public class ComplexExamples {



	@Ignore
	@Test
	public void testFastPaxos() throws Exception {
		String path = "src/test/resources/examples/FastPaxos/";
		StringBuilder sb = TestUtil.translate(path + "MCFastPaxos", "MCFastPaxos.cfg");
		System.out.println(sb);
		//String expected = fileToString(path + "AsynchInterface.mch");
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Ignore
	@Test
	public void testSecCtx() throws Exception {
		String path = "src/test/resources/examples/";
		StringBuilder sb = TestUtil.translate("SecCtx", "SecCtx.cfg");
		System.out.println(sb);
		//String expected = fileToString(path + "AsynchInterface.mch");
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test // TODO
	@Ignore
	public void testUf50_2() throws Exception {
		String path = "src/test/resources/examples/";
		StringBuilder sb = TestUtil.translate(path + "uf50_02.tla"); 
		TestUtil.getTreeAsString(sb.toString());
	}
	
	
}
