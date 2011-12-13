/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestUnchanged {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/unchanged/";
	static {
		path=path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}
	@Test
	public void testOneUnchangedVariable() throws Exception {
		ToolIO.reset();
		final String module = "-----MODULE OneUnchangedVariable-----\n"
				+ "VARIABLES a,b\n"
				+ "Init == a= 0 /\\ b = 0\n"
				+ "Next == a = 1 /\\ UNCHANGED b \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"OneUnchangedVariable.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSeveralUnchangedVariables() throws Exception {
		ToolIO.reset();
		final String module = "----- MODULE SeveralUnchangedVariables -----\n"
				+ "VARIABLES a,b,c,d,e\n"
				+ "Init == a= 0 /\\ b = 0 /\\ c = 0 /\\ d = 0 /\\ e = 0\n"
				+ "Next == a = 1 /\\ UNCHANGED <<b,c,d,e>> \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"SeveralUnchangedVariables.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
