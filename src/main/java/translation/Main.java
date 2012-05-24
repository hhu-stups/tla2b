package translation;

import analysis.InstanceTransformation;
import analysis.NewTypeChecker;
import analysis.SpecAnalyser;
import analysis.SymbolRenamer;
import analysis.SymbolSorter;
import config.ConfigfileEvaluator;
import config.ModuleOverrider;
import pprint.BMachinePrinter;
import exceptions.TLA2BException;
import global.TranslationGlobals;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Main implements TranslationGlobals {

	public static void main(String[] args) throws exceptions.FrontEndException,
			TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		String module = "----MODULE testing ----\n" 
				+ "CONSTANTS k \n" 
				+ "ASSUME k = 1" 
				+ "=======";
		final String config = "CONSTANTS k = 3";
		StringBuilder sb = Main.start(module, config, true);

		System.out.println(sb);
	}

	public static StringBuilder start(String fileName, String configName,
			boolean moduleAsString) throws exceptions.FrontEndException,
			TLA2BException, AbortException {
		String moduleName = fileName;
		if (!moduleAsString)
			moduleName = evalFileName(fileName);
		ModuleNode moduleNode = parseModule(moduleName);

		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		trans.start();

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();

		SpecAnalyser specAnalyser;
		ConfigfileEvaluator conEval = null;
		if (configName != null) {
			ModelConfig configAst = new ModelConfig(configName, null);
			configAst.parse();

			conEval = new ConfigfileEvaluator(configAst, moduleNode);
			conEval.start();

			ModuleOverrider modOver = new ModuleOverrider(moduleNode,
					conEval);
			modOver.start();
			specAnalyser = new SpecAnalyser(moduleNode, conEval);
		}else {
			specAnalyser = new SpecAnalyser(moduleNode);
		}

		specAnalyser.start();

		NewTypeChecker tc = new NewTypeChecker(moduleNode, conEval,
				specAnalyser);
		tc.start();
		
		specAnalyser.evalIfThenElse();
		
		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode,
				specAnalyser);
		symRenamer.start();

		BMachinePrinter p = new BMachinePrinter(moduleNode, conEval,
				specAnalyser);

		return p.start();

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
			throw new exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages())
							+ spec.parseErrors, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			throw new exceptions.FrontEndException(
					//allMessagesToString(ToolIO.getAllMessages())
							 ""+spec.semanticErrors, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages()), spec);
		}
		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length - 1; i++) {
			sb.append(allMessages[i] + "\n");
		}
		return sb.toString();
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

}
