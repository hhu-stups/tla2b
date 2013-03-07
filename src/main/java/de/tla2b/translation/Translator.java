package de.tla2b.translation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import de.tla2b.analysis.InstanceTransformation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.SymbolRenamer;
import de.tla2b.analysis.SymbolSorter;
import de.tla2b.analysis.TypeChecker;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ModuleOverrider;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.pprint.BMachinePrinter;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Translator implements TranslationGlobals {
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;
	private TypeChecker typechecker;

	public void start(String moduleFileName, String configFileName)
			throws TLA2BException {
		String moduleName = Translator.evalFileName(moduleFileName);
		moduleNode = parseModule(moduleName);

		modelConfig = null;
		if (configFileName != null) {
			modelConfig = new ModelConfig(configFileName, null);
			modelConfig.parse();
		}
	}
	
	public static StringBuilder translateString(String moduleString, String configString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Translator translator = new Translator();
		translator.startTest(moduleString, configString);
		return translator.translate();
	}

	public static void createTempfile(String moduleString){
		File dir = new File("temp/");
		dir.mkdirs();
		File tempFile = new File("temp/Testing.tla");
		try {
			tempFile.createNewFile();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		FileWriter fw;
		try {
			fw = new FileWriter(tempFile);
			fw.write(moduleString);
			fw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void startTest(String moduleString, String configString)
			throws de.tla2b.exceptions.FrontEndException, TLA2BException {

		createTempfile(moduleString);
		
		ToolIO.setUserDir("temp/");

		moduleNode = parseModule("Testing.tla");

		// TODO delete every time: finally
		File tempFile = new File("temp/Testing.tla");
		tempFile.delete();

		modelConfig = null;
		if (configString != null) {

			File configFile = new File("temp/Testing.cfg");
			try {
				configFile.createNewFile();
			} catch (IOException e1) {
				e1.printStackTrace();
			}

			FileWriter fw2;
			try {
				fw2 = new FileWriter(configFile);
				fw2.write(configString);
				fw2.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			modelConfig = new ModelConfig("Testing.cfg", null);
			modelConfig.parse();
		}
		File dir = new File("temp/");
		dir.delete();
	}

	public StringBuilder translate() throws TLA2BException {
		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		trans.start();

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();

		SpecAnalyser specAnalyser;

		ConfigfileEvaluator conEval = null;
		if (modelConfig != null) {

			conEval = new ConfigfileEvaluator(modelConfig, moduleNode);
			conEval.start();

			ModuleOverrider modOver = new ModuleOverrider(moduleNode, conEval);
			modOver.start();
			specAnalyser = new SpecAnalyser(moduleNode, conEval);
		} else {
			specAnalyser = new SpecAnalyser(moduleNode);
		}

		specAnalyser.start();

		typechecker = new TypeChecker(moduleNode, conEval, specAnalyser);
		typechecker.start();

		specAnalyser.evalIfThenElse();

		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();

		BMachinePrinter p = new BMachinePrinter(moduleNode, conEval,
				specAnalyser);

		return p.start();
	}

	public static ModuleNode parseModule(String moduleName)
			throws de.tla2b.exceptions.FrontEndException {

		SpecObj spec = new SpecObj(moduleName, null);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}

		if (spec.parseErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages())
							+ spec.parseErrors, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
			// allMessagesToString(ToolIO.getAllMessages())
					"" + spec.semanticErrors, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new de.tla2b.exceptions.FrontEndException(
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
	
	public ModuleNode getModuleNode() {
		return moduleNode;
	}

	public ModelConfig getModelConfig() {
		return modelConfig;
	}

	public TypeChecker getTypecheChecker(){
		return typechecker;
	}
	
}
