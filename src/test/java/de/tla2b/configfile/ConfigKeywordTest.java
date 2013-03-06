/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.configfile;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;
import org.junit.Test;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.util.Util;

public class ConfigKeywordTest {

	@Test
	public void TestConfig() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		StringBuilder sb = Util.translateString(module, config);
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
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Next == c' = c + 1 \n"
				+ "Inv == c \\in Nat \n"
				+ "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Util.translateString(module, config);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingNext() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Inv == c \\in Nat \n" + "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Util.translateString(module, config);
	}

	@Test(expected = ConfigFileErrorException.class)
	public void TestMissingInv() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES c \n"
				+ "Init == c = 1 \n"
				+ "Next == c' = c + 1 \n" + "=================================";
		final String config = "INIT Init NEXT Next INVARIANT Inv";
		Util.translateString(module, config);
	}
}
