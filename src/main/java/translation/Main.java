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
			sb = start(args[0], args[0], false);
		} catch (Exception e) {
			// ToolIO.printAllMessages();
			e.printStackTrace();
		}
		if (sb != null)
			System.out.println(sb);
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

		ModuleContext con = new ModuleContext(rootModule, config);

		if (config != null) {
			evalConfigFile(config, con);
		}

		ModuleTypeChecker mtc = new ModuleTypeChecker(rootModule, con);
		mtc.start();

		Translator t = new Translator();
		res = t.visitModule(rootModule, con);
		return res;
	}

	public static ModuleNode parseModule(String moduleName)
			throws exceptions.FrontEndException {

		SpecObj spec = new SpecObj(moduleName, null);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}


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

	public static void evalConfigFile(String configName,
			ModuleContext moduleContext) throws ConfigFileErrorException {

		ModelConfig configAst = new ModelConfig(configName + ".cfg", null);
		configAst.parse();

		ConfigTypeChecker configTC = new ConfigTypeChecker(configAst,
				moduleContext);
		configTC.start();
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
