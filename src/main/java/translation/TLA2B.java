package translation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;

import exceptions.MyException;

import util.FileUtil;
import util.ToolIO;

public class TLA2B {

	public static void main(String[] args) {
		ToolIO.setMode(ToolIO.TOOL);
		if (args.length != 1) {
			System.err.println("Require input file!");
			return;
		}
		String name = args[0];
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

		StringBuilder s = new StringBuilder();

		
		// Config file
		File config = new File(name + ".cfg");
		String configName = null;
		// use config if it exists
		if (config.exists()) {
			configName = name;
		}

		try {
			s = Main.start(name, configName, false);
		} catch (exceptions.FrontEndException e) {
			// error while parsing module (parse error or semantic error
			System.err.print(e.getMessage());
		} catch (MyException e) {
			System.err.print(e.getMessage());
		}

		if (s == null) {
			return;
		} else
			s.append("\n/* Created " + new Date() + " by TLA2B */");

		File f;
		f = new File(path + sourceModuleName + ".mch");
		try {
			f.createNewFile();
		} catch (IOException e) {
			e.printStackTrace();
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
			e.printStackTrace();
		}

	}

}
