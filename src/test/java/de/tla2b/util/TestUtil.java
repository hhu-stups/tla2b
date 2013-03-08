/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.translation.Tla2BTranslator;
import tla2sany.semantic.AbortException;
import util.FileUtil;
import util.ToolIO;

public class TestUtil {

	public static StringBuilder translateString(String moduleString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.startTest(moduleString, null);
		return translator.translate();
	}
	
	
	public static StringBuilder translateString(String moduleString, String configString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.startTest(moduleString, configString);
		return translator.translate();
	}
	
	
	public static StringBuilder translate(String moduleFileName)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.start(moduleFileName, null);
		StringBuilder res = translator.translate();
		return res;
	}
	
	public static StringBuilder translate(String moduleFileName, String configFileName)
			throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		configFileName = configFileName.replace('/', FileUtil.separatorChar);
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.start(moduleFileName, configFileName);
		return translator.translate();
	}
	
	
	public static TestTypeChecker typeCheckString(String moduleString) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, null);
		return testTypeChecker;
		
	}
	
	public static TestTypeChecker typeCheckString(String moduleString, String configString) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, configString);
		return testTypeChecker;
	}
	
	public static TestTypeChecker typeCheck(String moduleFileName) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.start(moduleFileName, null);
		return testTypeChecker;
	}
	
	public static TestTypeChecker typeCheck(String moduleFileName, String configFileName) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		configFileName = configFileName.replace('/', FileUtil.separatorChar);
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.start(moduleFileName, configFileName);
		return testTypeChecker;
	}


	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = in.readLine()) != null) {
			res.append(str + "\n");
		}
		in.close();
		return res.toString();
	}


	public static String getTreeAsString(final String testMachine)
			throws BException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);
	
		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}
	
	
}
