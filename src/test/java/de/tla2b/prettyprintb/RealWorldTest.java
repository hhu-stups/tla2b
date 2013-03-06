/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.util.Util;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

public class RealWorldTest {

	private static String path = "src/test/resources/prettyprint/realworld/";

	@Test
	public void testMicrowave() throws Exception {
		StringBuilder sb = Util.translate(path + "microwave", "microwave.cfg");
		String expected = fileToString(path + "microwave.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFowler() throws Exception {
		StringBuilder sb = Util.translate(path + "fowler");
		String expected = fileToString(path + "fowler.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testManyAssumes() throws Exception {
		StringBuilder sb = Util.translate(path + "ManyAssumes.tla");
		System.out.println(sb);
		//String expected = fileToString(path + "fowler.mch");
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Ignore
	@Test
	public void testFastPaxos() throws Exception {
		StringBuilder sb = Util.translate(path + "FastPaxos", "FastPaxos.cfg");
		//TODO 
		System.out.println(sb);
	}
	
}
