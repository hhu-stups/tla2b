package translation;

import java.io.PrintStream;
import java.util.Date;

import javax.tools.Tool;

import exceptions.ConfigFileErrorException;
import exceptions.ModuleErrorException;
import exceptions.TypeErrorException;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.SimpleFilenameToStream;
import util.ToolIO;

public class Mainold {
	// Gibt die erzeugte B-Maschine auf der Konsole aus
	public static void main(String[] args) {
		ToolIO.setMode(ToolIO.TOOL);
		StringBuilder sb;
		sb = start(args[0]);
		if (sb != null)
			System.out.println(sb);
	}

	public static String evalFileName(String name) {
		if (name.toLowerCase().endsWith(".tla")) {
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

	public static StringBuilder start(String fileName) {
		StringBuilder res = new StringBuilder();
		String mName = evalFileName(fileName);
		String configFile = mName;

		// Parser
		// SpecObj spec = new SpecObj(mName, new SimpleFilenameToStream());
		SpecObj spec = new SpecObj(mName, null);
		// PrintStream p = new PrintStream(new BufferedDataOutputStream());
		try {
			SANY.frontEndMain(spec, mName, ToolIO.out);
			// frontEndMain(spec, mName, null);
			//SANY.frontEndMain(spec, mName, p);
		} catch (FrontEndException e) {
			// Error in Frontend
			System.err.println("FrontEndException");
			return null;
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
		}

		// Parse Error
		if (spec.getParseErrors().isFailure()) {
			String[] messages = ToolIO.getAllMessages();
			for (int i = 0; i < messages.length; i++) {
				System.err.println(messages[i]);
			}
			System.err.println(spec.getParseErrors());
			return null;
		}

		// semantic Error
		if (spec.getSemanticErrors().isFailure()) {
			String[] messages = ToolIO.getAllMessages();
			for (int i = 0; i < messages.length; i++) {
				System.err.println(messages[i]);
			}
			return null;
		}

		if (n == null) { // Parse Error
			// ToolIO.printAllMessages();
			System.err.println("***Parse Error***");
			// String[] messages = ToolIO.getAllMessages();
			// for (int i = 0; i < messages.length; i++) {
			// System.err.println(messages[i]);
			// }
			// System.err.println(spec.getParseErrors());
			return null;
		}

		ModuleContext con = createModuleContext(n, configFile);
		
		// ModuleContext
		// ModuleContext con = new ModuleContext(config, n, configTC);

		// ModuleTypeChecker
		ModuleTypeChecker mtc = new ModuleTypeChecker(n, con);
		try {
			mtc.start();
		} catch (TypeErrorException e) {
			// System.out.println("TypeError" + e.getMessage());
			// e.printStackTrace();
			System.err.println("*** TypeError ***");
			System.err.println(e.getMessage());
			return null;
		} catch (ModuleErrorException e) {
			e.printStackTrace();
		} catch (MyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Translator t = new Translator();
		res = t.visitModule(n, con);
		return res;
	}

	public static ModuleContext createModuleContext(ModuleNode n,
			String configName) {

		if (configName == null) {
			return new ModuleContext(n);
		}

		// Configfile parsen
		ModelConfig config = new ModelConfig(configName + ".cfg", null);
		try {
			config.parse();
		} catch (Exception e) {
			System.err.println("Error in configuration file:");
			System.err.println(e.getMessage());
			return null;
		}

		ModuleContext con =new ModuleContext(n);
		
		// ConifgTypeChecker
		ConfigTypeChecker configTC = new ConfigTypeChecker(config, con);
		try {
			configTC.start();
		} catch (ConfigFileErrorException e) {
			System.err.println("TypeError in Configuration File:");
			System.err.println(e.getMessage());
			return null;
		}

		

		return con;
	}

	public static final void frontEndMain(SpecObj spec, String fileName,
			PrintStream syserr) throws FrontEndException {
		try {
			// **** Initialize the global environment
			SANY.frontEndInitialize(spec, syserr);

			// **** Parsing
			SANY.frontEndParse(spec, syserr);

			// **** Semantic analysis and level checking
			SANY.frontEndSemanticAnalysis(spec, syserr, true);
		} catch (InitException ie) {
			System.out.println("init");
			return;
		} catch (ParseException pe) {
			System.out.println("parse");
			return;
		} catch (SemanticException se) {
			System.out.println("semantic");
			System.out.println("hier");
			return;
		} catch (Exception e) {
			e.printStackTrace();
			// e.printStackTrace(syserr);
			// syserr.println(e.toString());
			throw new FrontEndException(e);
		}

		return;
	}

}