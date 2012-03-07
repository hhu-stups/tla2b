package util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import translation.Util;
import util.FileUtil;
import util.ToolIO;
public class TestUtil {

	public static String getTreeAsString(final String testMachine)
			throws BException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);

		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}



	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = in.readLine()) != null) {
			res.append(str + "\n");
		}
		in.close();
		return res.toString();
	}
	

	@Test
	public void TestGetPrefixWithoutLast(){
		String input = "foo!";
		assertEquals("", Util.getPrefixWithoutLast(input));
	}
	
	@Test
	public void TestGetPrefixWithoutLast2(){
		String input = "foo!bar!";
		assertEquals("foo!", Util.getPrefixWithoutLast(input));
	}
	
	@Test
	public void TestGetPrefixWithoutLast3(){
		String input = "";
		assertEquals("", Util.getPrefixWithoutLast(input));
	}
	
	@Test
	public void TestGetPrefixWithoutLast4(){
		String input = "foo!bar!bazz!";
		assertEquals("foo!bar!", Util.getPrefixWithoutLast(input));
	}
}
