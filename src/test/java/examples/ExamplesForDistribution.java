/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package examples;

import static org.junit.Assert.*;
import static util.TestUtil.fileToString;
import static util.TestUtil.getTreeAsString;

import org.junit.BeforeClass;
import org.junit.Test;

import translation.Main;
import util.FileUtil;
import util.ToolIO;

public class ExamplesForDistribution {

	private static String path = "src/test/resources/examples/";

	@BeforeClass
	public static void beforeClass(){
		path=path.replace('/', FileUtil.separatorChar);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testAsynchInterface() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("AsynchInterface", "AsynchInterface.cfg", false);
		String expected = fileToString(path + "AsynchInterface.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testChannel() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Channel", "Channel.cfg", false);
		System.out.println(sb);
		String expected = fileToString(path + "Channel.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testClub() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Club", "Club.cfg", false);
		String expected = fileToString(path + "Club.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testCounter() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Counter", "Counter.cfg", false);
		String expected = fileToString(path + "Counter.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDieHard() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("DieHard", "DieHard.cfg", false);
		String expected = fileToString(path + "DieHard.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDieHarder() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("DieHarder", "DieHarder.cfg", false);
		String expected = fileToString(path + "DieHarder.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testDoors() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Doors", "Doors.cfg", false);
		String expected = fileToString(path + "Doors.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testGraphIso() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("GraphIso", "GraphIso.cfg", false);
		String expected = fileToString(path + "GraphIso.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}

	@Test
	public void testHourClock() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("HourClock", "HourClock.cfg", false);
		System.out.println(sb);
		String expected = fileToString(path + "HourClock.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testJukebox() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Jukebox", "Jukebox.cfg", false);
		String expected = fileToString(path + "Jukebox.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testQueens() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Queens", "Queens.cfg", false);
		String expected = fileToString(path + "Queens.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testQueens2() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Queens2", "Queens2.cfg", false);
		String expected = fileToString(path + "Queens2.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testRecursiveFunction() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("RecursiveFunction", null, false);
		String expected = fileToString(path + "RecursiveFunction.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testScheduler() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("Scheduler", "Scheduler.cfg", false);
		System.out.println(sb);
		String expected = fileToString(path + "Scheduler.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test
	public void testSimpleSATProblem() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("SimpleSATProblem", null, false);
		String expected = fileToString(path + "SimpleSATProblem.mch");
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
	
	@Test // TODO
	public void testUf50_2() throws Exception {
		ToolIO.reset();
		StringBuilder sb = Main.start("uf50_02.tla", null, false); 
		getTreeAsString(sb.toString());
	}
	
}
