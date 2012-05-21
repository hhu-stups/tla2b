/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestSet {

	static {
		ToolIO.setMode(ToolIO.TOOL);
	}
	/**********************************************************************
	 * Set Enumeration: {1,2,3}
	 **********************************************************************/

	@Test
	public void testSetEnumeration() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1,2,3}\n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & k = {1,2,3} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSetEnumeration2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {TRUE, 1 = 1}\n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(BOOL) & k = {TRUE, bool(1=1)} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * Element of: \in, \notin
	 **********************************************************************/
	@Test
	public void testIn() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \\in BOOLEAN \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE : BOOL \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testIn2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 \\in {1,2,3} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : {1,2,3} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testNotIn() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 \\notin {} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 /: {} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * set operators like difference, union, intersection: \setdiff, \cup, \cap 
	 **********************************************************************/
	@Test
	public void testSetDifference() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1} = {1,2} \\ {1} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1} = {1,2} - {1} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testCup() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1,2} = {1} \\cup {2} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1,2} = {1} \\/ {2} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testCap() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1} = {1,2} \\cap {2} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1} = {1,2} /\\ {2} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * Subseteq: subset or equal
	 **********************************************************************/
	@Test
	public void testSubsteq() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE = ({1} \\subseteq {1,2}) \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = bool({1} <: {1,2}) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	/**********************************************************************
	 * SUBSET: conforms POW in B
	 **********************************************************************/
	@Test
	public void testSubset() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {{},{1}} = SUBSET {1,2} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {{},{1}} = POW({1,2}) \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * UNION
	 **********************************************************************/
	@Test
	public void testUnion() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME UNION {{1},{2}} = {1,2} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES union({{1},{2}}) = {1,2} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	/**********************************************************************
	 * Set Constructor
	 **********************************************************************/
	@Test
	public void testSubsetOf() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {x \\in {1,2} : x = 1} = {1} \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x | x : {1,2} & x = 1} = {1} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSetOfAll() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME {1} = {x + y+ 2:  x \\in {1,2}, y \\in {1} } \n"
				+ "=================================";
		
		StringBuilder sb = Main.start(module, null, true);
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1} = {t_|#x, y.(x : {1, 2} & y : {1} & t_ = x + y + 2)} \n" + "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
}
