package de.tla2b.main;

import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

import util.ToolIO;

import de.tla2b.translation.TLA2B;

public class MainTest {

	//TODO unknown error in combination of all tests
	@Ignore
	@Test
	public void testMainClassModule() throws Exception {
		String mainFile = "src/test/resources/main/counter.tla";
		TLA2B.main(new String[]{mainFile});
		assertFalse(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClassModule2() throws Exception {
		String mainFile = "src/test/resources/main/Counter";
		TLA2B.main(new String[]{mainFile});
		assertFalse(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClass2() throws Exception {
		ToolIO.reset();
		String mainFile = "src/test/resources/main/Test.tla";
		TLA2B.main(new String[]{mainFile});
		assertFalse(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClass3() throws Exception {
		String mainFile = "src/test/resources/main/Test.tla";
		TLA2B.main(new String[]{"-config", "Test.cfg", mainFile});
		assertFalse(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClass4() throws Exception {
		String mainFile = "src/test/resources/main/Counter.tla";
		TLA2B.main(new String[]{"-config", "Test.cfg", mainFile});
		assertFalse(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClassError() throws Exception {
		String mainFile = "src/test/resources/main/Tet.tla";
		TLA2B.main(new String[]{ mainFile});
		assertTrue(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testMainClassTypeError() throws Exception {
		String mainFile = "src/test/resources/main/TypeError.tla";
		TLA2B.main(new String[]{ mainFile});
		assertTrue(TLA2B.hasError());
	}
	
	@Ignore
	@Test
	public void testExternalCall() throws Exception {
		String mainFile = "src/test/resources/main/Test.tla";
		TLA2B.translateFile(mainFile);
		assertFalse(TLA2B.hasError());
	}
	
	
	
}
