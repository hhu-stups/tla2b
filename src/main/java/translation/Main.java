package translation;

import exceptions.ConfigFileErrorException;
import exceptions.MyException;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Main {

	public static void main(String[] args) {
		ToolIO.setMode(ToolIO.TOOL);
		StringBuilder sb = null;
		try {
			sb = start(args[0], null, false);
		} catch (Exception e) {
			// ToolIO.printAllMessages();
			e.printStackTrace();
		}
		if (sb != null)
			System.out.println(sb);
	}

	public static StringBuilder testing(String fileName, String configName)
			throws MyException, exceptions.FrontEndException {
		ToolIO.setMode(ToolIO.TOOL);

		String moduleName = evalFileName(fileName);
		String config = evalConfigName(configName);

		ModuleNode rootModule = parseModule(moduleName);
		if (rootModule == null) {
			throw new exceptions.FrontEndException("ParseError");
		}

		ModuleContext con = new ModuleContext(rootModule);
		if (config != null) {
			evalConfigFile2(config, con);
		}

		ModuleTypeChecker mtc = new ModuleTypeChecker(rootModule, con);
		mtc.start();

		Translator t = new Translator();
		StringBuilder res = t.visitModule(rootModule, con);

		return res;

	}

	public static StringBuilder start(String fileName, String configName,
			boolean moduleAsString) throws exceptions.FrontEndException,
			MyException {
		StringBuilder res = new StringBuilder();
		String moduleName = fileName;
		if (!moduleAsString)
			moduleName = evalFileName(fileName);
		String config = evalConfigName(configName);

		ModuleNode rootModule = parseModule(moduleName);

		ModuleContext con = new ModuleContext(rootModule);

		if (config != null) {
			boolean configCheck = evalConfigFile(config, con);
			if (!configCheck)
				return null;
		}

		ModuleTypeChecker mtc = new ModuleTypeChecker(rootModule, con);
		// try {
		mtc.start();
		// } catch (TypeErrorException e) {
		// // System.out.println("TypeError" + e.getMessage());
		// // e.printStackTrace();
		// System.err.println("*** TypeError ***");
		// System.err.println(e.getMessage());
		// return null;
		// } catch (ModuleErrorException e) {
		// e.printStackTrace();
		// } catch (MyException e) {
		// e.printStackTrace();
		// }

		Translator t = new Translator();
		res = t.visitModule(rootModule, con);
		return res;
	}

	public static ModuleNode parseModule(String moduleName)
			throws exceptions.FrontEndException {

		// Parser
		// SpecObj spec = new SpecObj(moduleName, new
		// MySimpleFilenameToStream());
		SpecObj spec = new SpecObj(moduleName, null);
		// PrintStream p = new PrintStream(new BufferedDataOutputStream());
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
			// frontEndMain(spec, mName, null);
			// SANY.frontEndMain(spec, mName, p);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}

		// // Parse Error
		// if (spec.getParseErrors().isFailure()) {
		//
		// throw new ParseErrorException(
		// allMessagesToString(ToolIO.getAllMessages()));
		// // throw new ParseErrorException(spec.getParseErrors().toString());
		// }
		//
		// // semantic error
		// if (spec.getSemanticErrors().isFailure()) {
		// throw new SemanticErrorException(
		// allMessagesToString(ToolIO.getAllMessages()));
		// // throw new
		// // SemanticErrorException(spec.getSemanticErrors().toString());
		// }

		if (spec.parseErrors.isFailure()) {
			throw new exceptions.FrontEndException(allMessagesToString(ToolIO.getAllMessages())+spec.parseErrors, spec);
		}
		
		if (spec.semanticErrors.isFailure()) {
			throw new exceptions.FrontEndException(allMessagesToString(ToolIO.getAllMessages())+spec.semanticErrors, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		// // Parse Error
		// if (spec.getParseErrors().isFailure()) {
		// String[] messages = ToolIO.getAllMessages();
		// for (int i = 0; i < messages.length; i++) {
		// System.err.println(messages[i]);
		// }
		// System.err.println(spec.getParseErrors());
		// return null;
		// }

		if (n == null) { // Parse Error
			System.out.println("Rootmodule null");
			throw new exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length-1; i++) {
			sb.append(allMessages[i] + "\n");
		}
		return sb.toString();
	}

	public static void evalConfigFile2(String configName,
			ModuleContext moduleContext) throws ConfigFileErrorException {

		ModelConfig configAst = new ModelConfig(configName + ".cfg", null);
		configAst.parse();

		ConfigTypeChecker configTC = new ConfigTypeChecker(configAst,
				moduleContext);
		configTC.start();
	}

	public static boolean evalConfigFile(String configName,
			ModuleContext moduleContext) {

		// parse config file
		ModelConfig configAst = new ModelConfig(configName + ".cfg", null);
		try {
			configAst.parse();
		} catch (Exception e) {
			System.err.println("Error in configuration file:");
			System.err.println(e.getMessage());
			return false;
		}

		// typecheck config File
		ConfigTypeChecker configTC = new ConfigTypeChecker(configAst,
				moduleContext);
		try {
			configTC.start();
		} catch (ConfigFileErrorException e) {
			System.err.println("Error in Configuration File:");
			System.err.println(e.getMessage());
			return false;
		}

		// no errors
		return true;
	}

	public static String evalFileName(String name) {
		if (name.toLowerCase().endsWith(".tla")) {
			name = name.substring(0, name.length() - 4);
		}

		if (name.toLowerCase().endsWith(".cfg")) {
			name = name.substring(0, name.length() - 4);
		}

		String sourceModuleName = name.substring(name
				.lastIndexOf(FileUtil.separator) + 1);

		String path = name.substring(0,
				name.lastIndexOf(FileUtil.separator) + 1);
		if (!path.equals(""))
			ToolIO.setUserDir(path);
		return sourceModuleName;
	}

	public static String evalConfigName(String name) {
		if (name == null)
			return null;
		if (name.toLowerCase().endsWith(".cfg")) {
			name = name.substring(0, name.length() - 4);
		}
		String configfile = name
				.substring(name.lastIndexOf(FileUtil.separator) + 1);

		return configfile;
	}

}
