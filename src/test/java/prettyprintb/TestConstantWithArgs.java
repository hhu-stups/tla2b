/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;


import org.junit.BeforeClass;
import org.junit.Test;

import exceptions.ConfigFileErrorException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestConstantWithArgs {
	private static String path = "src/test/resources/prettyprint/constantWithArgs/";
	
	@BeforeClass
	public static void beforeClass(){
		path=path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}
	/**********************************************************************
	 * Instance
	 **********************************************************************/


	@Test
	public void TestInstanceOpSubstitution() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE ModConstantAssignment ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "a \\prec b == a < b \n"
				+ "INSTANCE Counter WITH x <- c, start <- 0, \\prec <- \\prec  \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
//		String expected = fileToString(path+"ModConstantAssignment.mch");
//		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test (expected= ConfigFileErrorException.class)
	public void TestOpArgNotOverridenException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS c(_) \n"
				+ "ASSUME c(1) = 2 \n"
				+ "=================================";

		Main.start(module, null, true);
	}
	
}
