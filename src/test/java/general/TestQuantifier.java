package general;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;
import translation.Main;
import util.ToolIO;
import exceptions.FrontEndException;
import exceptions.TypeErrorException;

public class TestQuantifier {

	@Test
	public void ExistentialQuantification() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\E x \\in {1}: x < 2  \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES #x.(x : {1} & x < 2)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void UniversalQuantification() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME \\A x \\in {1}: x < 2 \n"
				+ "========================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES !x.(x : {1} => x < 2)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void QuantificationMoreVariables() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in {3,4},y \\in {1,2} : x>y \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES !x,y.(x : {3, 4} & y : {1, 2} => x > y)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void QuantificationMoreVariables2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x,y \\in {1,2} : x>y \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES !x,y.(x : {1, 2} & y : {1, 2} => x > y)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	// test types

	@Test(expected = TypeErrorException.class)
	public void TestSetType() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in 1 : TRUE \n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test(expected = TypeErrorException.class)
	public void TestBoolType() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in {1} : 2 \n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestConvert2Predicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in Nat : TRUE \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES !x.(x : NATURAL => TRUE = TRUE)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestTypeOfVariable() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\A x \\in Nat : x = TRUE \n"
				+ "=================================";
		Main.start(module, null, true);
	}

	// TLA+ allows no shadowing
	@Test(expected = FrontEndException.class)
	public void TestShadowing() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME \\E x \\in {1}: \\E x \\in {TRUE}: x  \n"
				+ "=================================";
		Main.start(module, null, true);
	}

}
