/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;
import exceptions.FrontEndException;
import exceptions.MyException;
import util.FileUtil;
import util.ToolIO;

public class TLA2B implements TranslationGlobals {

	public static void main(String[] args) {

		int i;
		String configName = null;
		for (i = 0; (i < args.length) && (args[i].charAt(0) == '-'); i++) {
			if (args[i].equals("-version")) {
				System.out.println("TLA2B version " + VERSION);
				System.exit(-1);
			} else if (args[i].equals("-config")) {
				i++;
				if (i < args.length) {
					if (args[i].toLowerCase().endsWith(".cfg")) {
						configName = args[i].substring(0, args[i].length() - 4);
					} else {
						configName = args[i];
					}
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

		String name = args[i];
		if (name.toLowerCase().endsWith(".tla")) {
			name = name.substring(0, name.length() - 4);
		}

		if (FileUtil.separator.equals("\\")) {
			name = name.replace("/", "\\");
		}

		String sourceModuleName = name.substring(name
				.lastIndexOf(FileUtil.separator) + 1);

		String path = name.substring(0,
				name.lastIndexOf(FileUtil.separator) + 1);

		// Config file
		File config;
		if (configName == null) {
			config = new File(name + ".cfg");
			// use config if it exists
			if (config.exists()) {
				configName = evalConfigName(configName);
			}else{
				configName = null;
			}
		}

		StringBuilder s = new StringBuilder();
		ToolIO.setMode(ToolIO.TOOL);
		try {
			s = Main.start(name, configName, false);
		} catch (FrontEndException e) {
			System.err.println(e.getMessage());
			System.exit(-1);
		} catch (MyException e) {
			System.err.print("**** Translation Error ****\n");
			System.err.println(e.getMessage());
			System.exit(-1);
		}

		s.append("\n/* Created " + new Date() + " by TLA2B */");

		File f;
		f = new File(path + sourceModuleName + ".mch");
		try {
			f.createNewFile();
		} catch (IOException e) {
			System.err.println(String.format("Could not create File %s.", path
					+ sourceModuleName + ".mch"));
			return;
		}

		Writer fw = null;
		try {
			String res = s.toString();
			fw = new FileWriter(f);
			fw.write(res);
			fw.close();
			System.out.println("B-Maschine " + sourceModuleName
					+ ".mch created.");
		} catch (IOException e) {
			System.err.println("Error while creating file " + sourceModuleName
					+ "mch.");
		}
	}
	
	public static String evalConfigName(String name) {
		if (name == null)
			return null;
		if (!name.toLowerCase().endsWith(".cfg")) {
			name = name + ".cfg";
		}
		String configfile = name
				.substring(name.lastIndexOf(FileUtil.separator) + 1);

		return configfile;
	}
}
