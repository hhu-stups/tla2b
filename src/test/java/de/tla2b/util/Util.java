/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.util;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.translation.Translator;
import tla2sany.semantic.AbortException;
import util.FileUtil;
import util.ToolIO;

public class Util {

	public static StringBuilder translateString(String moduleString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Translator translator = new Translator();
		translator.startTest(moduleString, null);
		return translator.translate();
	}
	
	
	public static StringBuilder translateString(String moduleString, String configString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Translator translator = new Translator();
		translator.startTest(moduleString, configString);
		return translator.translate();
	}
	
	
	public static StringBuilder translate(String moduleFileName)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		Translator translator = new Translator();
		translator.start(moduleFileName, null);
		return translator.translate();
	}
	
	public static StringBuilder translate(String moduleFileName, String configFileName)
			throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		configFileName = configFileName.replace('/', FileUtil.separatorChar);
		Translator translator = new Translator();
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
	
	
}
