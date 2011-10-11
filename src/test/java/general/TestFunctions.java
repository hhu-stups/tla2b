package general;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import exceptions.TypeErrorException;
import translation.Main;
import util.ToolIO;

public class TestFunctions {

	@Test
	public void TestFunction() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f == [x \\in Nat |-> x+1]\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestFunction2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestFunctionCall() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME f[1] = 2\n" + "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "PROPERTIES f(1) = 2"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestDomain() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME DOMAIN f = Nat" + "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES dom(f) = NATURAL\n"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestDomainType() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n" + "f[x \\in Nat] ==  x+1\n"
				// same Type
				+ "ASSUME DOMAIN f = {1}" + "=================================";
		Main.start(module, null, true);
	}

	@Test(expected = TypeErrorException.class)
	public void TestDomainType2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n" + "f[x \\in Nat] ==  x+1\n"
				// different types
				+ "ASSUME DOMAIN f = 1" + "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestSetOfFunction() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME [Nat -> BOOLEAN] = [{1,2} -> {TRUE}]"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES NATURAL --> BOOL = {1,2} --> {TRUE}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestSetOfFunctionTypes() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "foo == [Nat -> 1]"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test(expected = TypeErrorException.class)
	public void TestSetOfFunctionTypes2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "ASSUME [Nat -> BOOLEAN ] = [BOOLEAN -> Nat]"
				+ "=================================";
		Main.start(module, null, true);
	}

	@Test
	public void TestExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME [f EXCEPT ![1] = 1] # f"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (f <+ {1 |-> 1}) /= f\n"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void TestExcept2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME [f EXCEPT ![1] = 1, ![2] = 2, ![3]= 3] # f"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (f <+ {1 |-> 1, 2 |-> 2, 3 |-> 3}) /= f\n"
				+ "DEFINITIONS f ==  %x.(x : NATURAL | x+1)\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test(expected = TypeErrorException.class)
	public void TestExceptTypes() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME [f EXCEPT ![TRUE] = 1] # f"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
	}

	@Test(expected = TypeErrorException.class)
	public void TestExceptTypes2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "f[x \\in Nat] ==  x+1\n"
				+ "ASSUME [f EXCEPT ![1] = TRUE] # f"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);
	}

	@Test
	public void TestExceptTypes3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals\n"
				+ "CONSTANTS f\n"
				+ "foo == [f EXCEPT ![1] = 1]"
				+ "=================================";
		StringBuilder sb = Main.start(module, null, true);

		final String expected = "MACHINE Testing\n" + "CONSTANTS f\n"
				+ "PROPERTIES f : POW(INTEGER*INTEGER)\n"
				+ "DEFINITIONS foo ==  f <+ {1|->1}\n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

}
