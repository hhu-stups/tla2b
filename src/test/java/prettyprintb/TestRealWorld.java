/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import org.junit.BeforeClass;
import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;
import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

public class TestRealWorld {

	private static String path = "src/test/resources/prettyprint/realworld/";

	@BeforeClass
	public static void beforeClass(){
		path=path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testQueens() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Queens", null, false);
		String expected = fileToString(path + "Queens.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testMicrowave() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("microwave", "microwave.cfg", false);
		String expected = fileToString(path + "microwave.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFowler() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("fowler", null, false);
		String expected = fileToString(path + "fowler.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testFastPaxos() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("FastPaxos", "FastPaxos.cfg", false);
		System.out.println(sb);
	}
	
}
