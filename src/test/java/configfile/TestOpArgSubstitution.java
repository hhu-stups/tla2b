/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package configfile;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.Ignore;
import org.junit.Test;

import exceptions.FrontEndException;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class TestOpArgSubstitution {

	@Test
	public void testConstantWithArgsOverriddenByDef() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_) \n"
				+ "foo(a,b) == a+b \n"
				+ "ASSUME k(1,2) = 3"
				+ "=================================";
		final String config = "CONSTANTS k <- foo";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo(1, 2) = 3 \n"
				+ "DEFINITIONS foo(a,b) == a + b \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = FrontEndException.class)
	public void testOpArgNoSubstitutionException() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE OpArgNode ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "plus(a,b) == a + b \n"
				+ "foo(bar(_,_),a,b) == bar(a,b) \n"
				+ "ASSUME foo(plus, 1,3) = 4 \n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void testOpArgOverriddenByInfixOp() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k(_,_) \n"
				+ "ASSUME k(1,2) \n" + "=================================";
		final String config = "CONSTANTS k <- < ";
		StringBuilder sb = Main.start(module, config, true);
		final String expected = "MACHINE Testing\n" + "PROPERTIES 1 < 2 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
