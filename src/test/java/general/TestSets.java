package general;

import org.junit.Ignore;
import org.junit.Test;

import exceptions.TypeErrorException;
import translation.Main;
import util.ToolIO;
import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

public class TestSets {

	@Test
	public void TestSetEnumeration() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1,2,3}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & k = {1,2,3}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestSetEnumerationTypes() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1,2,TRUE}\n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestElementOf() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k \\in {1,2,3}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER & k : {1,2,3}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestNotElementOf() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME 1 \\notin k\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & 1 /: k\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestElementOfTypes() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k \\in 1\n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestCap() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo == k \\cap {1,2,3}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER)\n"
				+ "DEFINITIONS foo == k /\\ {1,2,3}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestCup() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo == {1,2,3} \\cup {k}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : INTEGER\n"
				+ "DEFINITIONS foo == {1,2,3} \\/ {k}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestCupOrCapTypes() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo == {1,2,3} \\cup {TRUE}\n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test(expected = TypeErrorException.class)
	public void TestCupOrCapTypes2() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo == 1 \\cup 1\n"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestSubseteq() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k \\subseteq {1,2}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & k <: {1,2}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestSetdifferenz() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "foo == k \\{1,2}\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER)\n"
				+ "DEFINITIONS foo == k - {1,2}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void TestSetConstructor() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ "foo == k = {x \\in Nat : x>2} \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER)\n"
				+ "DEFINITIONS foo == k = {x| x : NATURAL & x>2}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test(expected = TypeErrorException.class)
	public void TestSetConstructorTypes() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ "foo == k = {x \\in Nat : 2} \n"
				+ "=================================";
		Main.start(module, null, true);
	}
	
	@Test(expected = TypeErrorException.class)
	public void TestSetConstructorTypes2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ "foo == k = {x \\in 1 : TRUE} \n"
				+ "=================================";
		Main.start(module, null, true);
	}
	
	@Test
	public void TestSetConstructor2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS k\n"
				+ "foo == k = {x*x : x \\in Nat} \n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER)\n"
				+ "DEFINITIONS foo == k = {t_|#x.(x : NATURAL & t_ = x * x)}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
