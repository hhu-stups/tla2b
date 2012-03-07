/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import exceptions.ConfigFileErrorException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestInstanceConstantSubstitution {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/instance/constantSubstitution/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void TestExp4Con() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c \n"
				+ "INSTANCE Value WITH val <- 1+1  \n"
				+ "ASSUME def"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS c \n"
				+ "PROPERTIES c : INTEGER & def \n"
				+ "DEFINITIONS def == c = 1 + 1 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestCon4Con() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c, val2 \n"
				+ "INSTANCE Value WITH val <- val2   \n"
				+ "ASSUME def /\\ val2 = 1"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS c, val2 \n"
				+ "PROPERTIES c : INTEGER & val2 : INTEGER & def & val2 = 1 \n"
				+ "DEFINITIONS def == c = val2 \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestDef4OpArg() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c2 \n"
				+ " bar(a,b) == a + b  "
				+ "INSTANCE OpArg WITH c <- c2, foo <- bar \n"
				+ "ASSUME def /\\ c2 = 3 \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing \n"
				+ "ABSTRACT_CONSTANTS c2 \n"
				+ "PROPERTIES c2 : INTEGER & def & c2 = 3 \n"
				+ "DEFINITIONS bar(a,b) == a + b; def == c2 = bar(1, 2)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test (expected = ConfigFileErrorException.class)
	public void TestOpArg4OpArgException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c2, bar(_,_) \n"
				+ "INSTANCE OpArg WITH c <- c2, foo <- bar \n"
				+ "ASSUME def /\\ c2 = 3 \n"
				+ "=================================";

		Main.start(module, null, true);
	}
	
	@Test
	public void TestOpArg4OpArg() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c2, bar(_,_) \n"
				+ "bazz(a,b) == a + b \n"
				+ "INSTANCE OpArg WITH c <- c2, foo <- bar \n"
				+ "ASSUME def /\\ c2 = 3 \n"
				+ "=================================";
		final String config = "CONSTANTS bar <- bazz";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing \n"
				+ "ABSTRACT_CONSTANTS c2 \n"
				+ "PROPERTIES c2 : INTEGER & def & c2 = 3 \n"
				+ "DEFINITIONS bazz(a,b) == a + b; def == c2 = bazz(1, 2)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestInstanced2Times() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS c3, foo3(_,_) \n"
				+ "bazz(a,b) == a + b \n"
				+ "INSTANCE InstancingOpArg WITH c2 <- c3, foo2 <- foo3 \n"
				+ "ASSUME def /\\ c3 = 3 \n"
				+ "=================================";
		final String config = "CONSTANTS foo3 <- bazz";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing \n"
				+ "ABSTRACT_CONSTANTS c3 \n"
				+ "PROPERTIES c3 : INTEGER & def & c3 = 3 \n"
				+ "DEFINITIONS bazz(a,b) == a + b; def == c3 = bazz(1, 2)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
}
