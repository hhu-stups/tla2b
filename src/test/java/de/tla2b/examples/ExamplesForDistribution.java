/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.examples;

import static de.tla2b.util.TestUtil.fileToString;
import static de.tla2b.util.TestUtil.getTreeAsString;
import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

import de.tla2b.util.Util;


public class ExamplesForDistribution {

	@Test
	public void testAsynchInterface() throws Exception {
		String path = "src/test/resources/examples/AsynchInterface/";
		StringBuilder sb = Util.translate(path + "AsynchInterface.tla", "AsynchInterface.cfg");
		String expected = fileToString(path + "AsynchInterface.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testChannel() throws Exception {
		String path = "src/test/resources/examples/Channel/";
		StringBuilder sb = Util.translate(path + "Channel.tla", "Channel.cfg");
		String expected = fileToString(path + "Channel.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testClub() throws Exception {
		String path = "src/test/resources/examples/Club/";
		StringBuilder sb = Util.translate(path + "Club.tla", "Club.cfg");
		String expected = fileToString(path + "Club.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCounter() throws Exception {
		String path = "src/test/resources/examples/Counter/";
		StringBuilder sb = Util.translate(path + "Counter", "Counter.cfg");
		String expected = fileToString(path + "Counter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDieHard() throws Exception {
		String path = "src/test/resources/examples/DieHard/";
		StringBuilder sb = Util.translate(path + "DieHard", "DieHard.cfg");
		String expected = fileToString(path + "DieHard.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	


	@Test
	public void testDieHarder() throws Exception {
		String path = "src/test/resources/examples/DieHard/";
		StringBuilder sb = Util.translate(path + "DieHarder", "DieHarder.cfg");
		String expected = fileToString(path + "DieHarder.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDoors() throws Exception {
		String path = "src/test/resources/examples/Doors/";
		StringBuilder sb = Util.translate(path + "Doors", "Doors.cfg");
		String expected = fileToString(path + "Doors.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testGraphIso() throws Exception {
		String path = "src/test/resources/examples/GraphIso/";
		StringBuilder sb = Util.translate(path+ "GraphIso", "GraphIso.cfg");
		String expected = fileToString(path + "GraphIso.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testHourClock() throws Exception {
		String path = "src/test/resources/examples/HourClock/";
		StringBuilder sb = Util.translate(path + "HourClock", "HourClock.cfg");
		String expected = fileToString(path + "HourClock.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testJukebox() throws Exception {
		String path = "src/test/resources/examples/JukeBox/";
		StringBuilder sb = Util.translate(path + "Jukebox", "Jukebox.cfg");
		String expected = fileToString(path + "Jukebox.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testQueens() throws Exception {
		String path = "src/test/resources/examples/Queens/";
		StringBuilder sb = Util.translate(path + "Queens", "Queens.cfg");
		String expected = fileToString(path + "Queens.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testQueens2() throws Exception {
		String path = "src/test/resources/examples/Queens/";
		StringBuilder sb = Util.translate(path + "Queens2", "Queens2.cfg");
		String expected = fileToString(path + "Queens2.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecursiveFunction() throws Exception {
		String path = "src/test/resources/examples/RecursiveFunction/";
		StringBuilder sb = Util.translate(path + "RecursiveFunction");
		String expected = fileToString(path + "RecursiveFunction.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testScheduler() throws Exception {
		String path = "src/test/resources/examples/Scheduler/";
		StringBuilder sb = Util.translate(path + "Scheduler", "Scheduler.cfg");
		String expected = fileToString(path + "Scheduler.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSimpleSATProblem() throws Exception {
		String path = "src/test/resources/examples/SimpleSATProblem/";
		StringBuilder sb = Util.translate(path + "SimpleSATProblem");
		String expected = fileToString(path + "SimpleSATProblem.mch");
		System.out.println(sb);
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDefCapture() throws Exception {
		String path = "src/test/resources/examples/DefCapture/";
		StringBuilder sb = Util.translate(path + "DefCapture");
		String expected = fileToString(path + "DefCapture.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	
}
