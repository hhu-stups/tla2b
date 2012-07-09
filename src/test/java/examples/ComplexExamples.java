/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package examples;


import org.junit.BeforeClass;
import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class ComplexExamples {

	private static String path = "src/test/resources/examples/FastPaxos";

	@BeforeClass
	public static void beforeClass(){
		path=path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testAsynchInterface() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("MCFastPaxos", "MCFastPaxos.cfg", false);
		System.out.println(sb);
		//String expected = fileToString(path + "AsynchInterface.mch");
		//assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
