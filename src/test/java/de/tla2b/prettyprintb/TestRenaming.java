package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.translation.Translator;
import de.tla2b.util.Util;

import util.ToolIO;

public class TestRenaming {

	
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}


	@Test
	public void testLetOperators() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME LET right == 1 IN right = 2\n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES right_1 = 2 \n" 
				+ "DEFINITIONS right_1 == 1 \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testRenamingSpecialCharacter() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ " a \\prec b == a = b\n"
				+ "ASSUME 1 \\prec 2\n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES prec(1, 2) \n" 
				+ "DEFINITIONS prec(a,b) == a = b \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testEliminatingSlashes() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ " a \\prec b == a = b\n"
				+ "ASSUME 1 \\prec 2\n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES prec(1, 2) \n" 
				+ "DEFINITIONS prec(a,b) == a = b \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testBBuiltInOperatorOusideOfStandardModule() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ " a < b == a = b\n"
				+ "ASSUME 1 < 2\n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES lt(1, 2) \n" 
				+ "DEFINITIONS lt(a, b) == a = b \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testExistentialQuantificationWithDuplicateVariableName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def == \\E x \\in {1,2}: x = 1\n"
				+ "ASSUME \\E x \\in {1,2}: def \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES #x.(x : {1, 2} & def) \n" 
				+ "DEFINITIONS def == #x_1.(x_1 : {1, 2} & x_1 = 1)\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	

	
	@Test
	public void testSetBuilderWithDuplicateVariableName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def == \\E x \\in {1}: x = 1 \n"
				+ "ASSUME {x \\in {1,2,3}: def } = {1} \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x|x : {1, 2, 3} & def} = {1} \n" 
				+ "DEFINITIONS def == #x_1.(x_1 : {1} & x_1 = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testSetBuilder2WithDuplicateVariableName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def ==  \\E x \\in {1}: x = 1\n"
				+ "ASSUME {def : x \\in {1,2,3}} = {TRUE} \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {t_|#x.(x : {1, 2, 3} & t_ = bool(def))} = {TRUE} \n" 
				+ "DEFINITIONS def == #x_1.(x_1 : {1} & x_1 = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testChooseWithDuplicateVariableName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def == \\E x \\in {1}: x = 1 \n"
				+ "ASSUME 1 = CHOOSE x \\in {1,2}: def \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 = CHOOSE({x|x : {1, 2} & def}) \n" 
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T); \n"
				+ " def == #x_1.(x_1 : {1} & x_1 = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
	@Test
	public void testFunctionConstructorWithDuplicateVariableName() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def == \\E x \\in {1}: x = 1 \n"
				+ "ASSUME [x \\in {1,2,3} |-> def] \\in [{1,2,3} -> {TRUE}] \n"
				+ "=================================";
		
		StringBuilder sb = Util.translateString(module);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES %x.(x : {1, 2, 3}| bool(def)) : {1, 2, 3} --> {TRUE} \n" 
				+ "DEFINITIONS def == #x_1.(x_1 : {1} & x_1 = 1) \n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
