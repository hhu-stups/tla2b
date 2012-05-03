/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import exceptions.ConfigFileErrorException;

import translation.Main;
import util.ToolIO;

public class TestConfigKeywords {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	@Test
	public void TestConfig() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		StringBuilder sb = Main.start(module, config, true);
		System.out.println(sb);
		String expected = "MACHINE Testing\n"
				+ "DEFINITIONS Inv == c : NATURAL \n" + "VARIABLES c \n"
				+ "INVARIANT c: INTEGER & Inv \n" + "INITIALISATION c:(c=1) \n"
				+ "OPERATIONS Next_Op = ANY c_n \n"
				+ "WHERE c_n : INTEGER & c_n = c+ 1 \n"
				+ "THEN c:= c_n END END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingInit() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Main.start(module, config, true);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingNext() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Inv == c \\in Nat \n" + "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Main.start(module, config, true);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingInv() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n" + "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Main.start(module, config, true);
	}
}
