package translation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import util.FileUtil;

//Speichert die erzeugte B-Maschine in dem selben Ordner im dem sich das TLA Modul befindet
//Der Name entspricht dem Namen des Moduls und hat die Endung .mch
public class Main2 {

	public static void main(String[] args) {
		if (args.length != 1) {
			System.err.println("Require input file!");
			return;
		}
		String name = args[0];

		if (name.toLowerCase().endsWith(".tla")) {
			name = name.substring(0, name.length() - 4);
		}
		if(FileUtil.separator.equals("\\")){
			name = name.replace("/", "\\");
		}

		String sourceModuleName = name.substring(name
				.lastIndexOf(FileUtil.separator) + 1);

		String path = name.substring(0,
				name.lastIndexOf(FileUtil.separator) + 1);

		StringBuilder s = new StringBuilder();

		s = Main.start(name,name);
		if (s == null) {
			return;
		}

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
			e.printStackTrace();
		}

	}

}
