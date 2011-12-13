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

public class TLA2B {

	public static void main(String[] args) {

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

		// Config file
		File config = new File(name + ".cfg");
		String configName = null;
		// use config if it exists
		if (config.exists()) {
			configName = name + ".cfg";
		}

		StringBuilder s = new StringBuilder();

		ToolIO.setMode(ToolIO.TOOL);
		try {
			s = Main.start(name, configName, false);
		} catch (FrontEndException e) {
			System.err.println(e.getMessage());
			return;
		} catch (MyException e) {
			System.err.print("**** Translation Error ****\n");
			System.err.println(e.getMessage());
			return;
		}

		s.append("\n/* Created " + new Date() + " by TLA2B */");

		File f;
		f = new File(path + sourceModuleName + ".mch");
		try {
			f.createNewFile();
		} catch (IOException e) {
			// TODO
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
}
