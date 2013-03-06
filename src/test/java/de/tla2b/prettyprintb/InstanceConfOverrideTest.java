/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.Util;



public class InstanceConfOverrideTest {

	
	private static String path = "src/test/resources/prettyprint/instance/configOverride/";

	@Test
	public void testInstanceDefOverride() throws Exception {
		StringBuilder sb = Util.translate(path + "InstanceCounter.tla", "InstanceCounter.cfg");
		String expected = fileToString(path + "InstanceCounter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Ignore //TODO find Exception
	@Test //(expected = ConfigFileErrorException.class)
	public void testInstanceConOverrideException() throws Exception {
		StringBuilder sb = Util.translate(path + "InstanceCounterException.tla", "InstanceCounterException.cfg");
		System.out.println(sb);
	}
	
	@Ignore
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS a <-[Counter] def";

		Util.translateString(module);
	} 
	@Ignore
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS val <-[Cou] def";

		Util.translateString(module);
	}
	@Ignore
	@Test (expected = ConfigFileErrorException.class)
	public void testInstanceDefOverrideException3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start VARIABLES x\n"
				+ "INSTANCE Counter \n" + "=================================";
		final String config = "INIT Init\n" + "NEXT Next \n"
				+ "CONSTANTS val <-[Counter] d";

		Util.translateString(module);
	}
	
}
