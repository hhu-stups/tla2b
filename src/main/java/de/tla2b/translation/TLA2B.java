/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.translation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import util.FileUtil;
import util.ToolIO;

public class TLA2B implements TranslationGlobals {
	private String mainFile;
	private String path;
	private String configFileName;
	private String mainModuleName;

	private static boolean error = false;

	public static boolean hasError() {
		return error;
	}

	public TLA2B() {
		mainFile = null;
		path = null;
		configFileName = null;
		mainModuleName = null;
	}

	public void handleParameter(String[] args) {
		int i;
		for (i = 0; (i < args.length) && (args[i].charAt(0) == '-'); i++) {
			if (args[i].equals("-version")) {
				System.out.println("TLA2B version " + VERSION);
				System.exit(-1);
			} else if (args[i].equals("-expr")) {
				if (i + 1 == args.length) {
					System.err.println("Error: expected a module file.");
					System.exit(-1);
				}
				evalExpression(args[i + 1]);
				return;
			}

			else if (args[i].equals("-config")) {
				i++;
				if (i < args.length) {
					configFileName = args[i];
				} else {
					System.err
							.println("Error: expect a file name for -config option.");
				}

			} else {
				System.err.println("Illegal switch: " + args[i]);
				System.exit(-1);
			}
		}

		if (i == args.length) {
			System.err.println("Error: expected a module file.");
			System.exit(-1);
		}
		mainFile = args[i];
	}

	private void evalModuleFileName() {
		String name = mainFile;
		if (name.toLowerCase().endsWith(".tla")) {
			name = name.substring(0, name.length() - 4);
		}

		name = name.replace("\\", File.separator);
		name = name.replace("/", File.separator);

		mainModuleName = name
				.substring(name.lastIndexOf(FileUtil.separator) + 1);

		path = name.substring(0, name.lastIndexOf(FileUtil.separator) + 1);

		if (path.equals("")) {
			ToolIO.setUserDir("." + File.separator);
		} else {
			ToolIO.setUserDir(path);
		}

	}

	private void evalConfigFile() {
		// Config file
		File file;
		if (configFileName == null) {

			file = new File(path + mainModuleName + ".cfg");
			// use config if it exists
			if (file.exists()) {
				configFileName = mainModuleName + ".cfg";
			}
		} else {
			// user input
			if (!configFileName.toLowerCase().endsWith(".cfg")) {
				configFileName = configFileName + ".cfg";
			}
		}
	}

	public static void main(String[] args) {
		TLA2B tla2b = new TLA2B();
		tla2b.handleParameter(args);

		tla2b.evalModuleFileName();
		tla2b.evalConfigFile();

		ToolIO.setMode(ToolIO.TOOL);
		Tla2BTranslator t = new Tla2BTranslator();
		try {
			t.start(tla2b.mainModuleName, tla2b.configFileName);
		} catch (FrontEndException e) {
			error = true;
			System.err.println(e.getMessage());
			System.exit(1);
		} catch (TLA2BException e) {
			error = true;
			System.err.println(e.getMessage());
			System.exit(1);
		} catch (RuntimeException e) {
			error = true;
			System.err.println(e.getMessage());
			System.exit(1);
		}

		StringBuilder s = new StringBuilder();
		try {
			s = t.translate();
		} catch (TLA2BException e) {
			error = true;
			System.err.print("**** Translation Error ****\n");
			System.err.println(e.getMessage());
			return;
		}
		s.insert(0, "/*@ generated by TLA2B " + VERSION + " " + new Date()
				+ " */\n");
		// s.append("\n/* Created " + new Date() + " by TLA2B */");

		tla2b.createMachineFile(s);

	}

	private void createMachineFile(StringBuilder s) {
		String machineFileName = path + mainModuleName + "_tla.mch";
		File machineFile;
		machineFile = new File(machineFileName);
		if (machineFile.exists()) {
			try {
				BufferedReader in;

				in = new BufferedReader(new FileReader(machineFile));

				String firstLine = null;
				firstLine = in.readLine();
				if (!firstLine.startsWith("/*@ generated by TLA2B ")) {
					System.err.println("Error: File " + machineFileName
							+ " already exists"
							+ " and was not generated by TLA2B.\n"
							+ "Delete or move this file.");
					in.close();
					System.exit(1);
				}
				in.close();
			} catch (IOException e) {
				System.err.println(e.getMessage());
				System.exit(1);
			}
		}

		try {
			machineFile.createNewFile();
		} catch (IOException e) {
			System.err.println(String.format("Could not create File %s.",
					machineFileName));
			System.exit(1);
		}

		Writer fw = null;
		try {
			String res = s.toString();
			fw = new FileWriter(machineFile);
			fw.write(res);
			fw.close();
			System.out.println("B-Machine " + mainModuleName
					+ "_tla.mch created.");
		} catch (IOException e) {
			System.err.println("Error while creating file " + mainModuleName
					+ "mch.");
			System.exit(1);
		}

	}

	public static String translateFile(String mainFile) throws TLA2BException {
		TLA2B tla2b = new TLA2B();
		tla2b.mainFile = mainFile;
		tla2b.evalModuleFileName();
		Tla2BTranslator t = new Tla2BTranslator();
		t.start(tla2b.mainModuleName, tla2b.configFileName);
		StringBuilder s = t.translate();
		return s.toString();
	}

	/**
	 * @throws IOException
	 * 
	 */
	private static void evalExpression(String file) {

		ToolIO.setMode(ToolIO.TOOL);
		String expr = null;
		try {
			expr = fileToString(file);
		} catch (IOException e) {
			e.printStackTrace();
		}
		ExpressionTranslator et = new ExpressionTranslator(expr);
		try {
			et.start();
		} catch (TLA2BException e) {
			System.err.println("------ExpressionError----------------");
			System.err.println(e.getMessage());
		}

	}

	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		boolean first = true;
		while ((str = in.readLine()) != null) {
			if (!first)
				res.append("\n");
			res.append(str);
		}
		in.close();
		return res.toString();
	}
}
