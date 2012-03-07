/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.*;

import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestInstance {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/instance/";
	static {
		path=path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}
	/**********************************************************************
	 * Instance
	 **********************************************************************/

	@Test
	public void testOneInstanced() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE OneInstanced ----------------\n"
				+ "CONSTANTS start \n"
				+ "VARIABLES c \n"
				+ "count == INSTANCE Counter WITH x <- c  \n"
				+ "Init == count!Init\n"
				+ "Next == count!Next\n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"OneInstanced.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testTwoInstanced() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE TwoInstanced ----------------\n"
				+ "CONSTANTS start \n"
				+ "VARIABLES c, c2 \n"
				+ "count == INSTANCE Counter WITH x <- c  \n"
				+ "count2 == INSTANCE Counter WITH x <- c2, start <- 0  \n"
				+ "Init == count!Init /\\ count2!Init\n"
				+ "Next == 	\\/ (count!Next /\\ UNCHANGED c2) \n"
				+ "			\\/ (count2!Next /\\ UNCHANGED c) \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"TwoInstanced.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testInstanceNoName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE InstanceNoName ----------------\n"
				+ "CONSTANTS start \n"
				+ "VARIABLES c \n"
				+ "INSTANCE Counter WITH x <- c  \n"
				+ "Spec == Init /\\ [][Next]_c "
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"InstanceNoName.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestInstanceOpArg() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE InstanceOpArg ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "foo(a,b) == a + b \n"
				+ "INSTANCE OpArg WITH k <- foo \n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"InstanceOpArg.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestInstanceDefinition() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE InstanceDefinition ----------------\n"
				+ "VARIABLES c \n"
				+ " val == 5 \n"
				+ "INSTANCE Counter WITH x <- c, start <- 0\n"
				+ "=================================";

		StringBuilder sb = Main.start(module, null, true);
		String expected = fileToString(path+"InstanceDefinition.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestModConstantAssignment() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE ModConstantAssignment ----------------\n"
				+ "VARIABLES c \n"
				+ "INSTANCE Counter WITH x <- c, start <- 0\n"
				+ "=================================";
		final String config = "INIT Init\n"
				+ "NEXT Next \n"
				+ "CONSTANTS val = [Counter] 7";
		
		StringBuilder sb = Main.start(module, config, true);
		String expected = fileToString(path+"ModConstantAssignment.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
}
