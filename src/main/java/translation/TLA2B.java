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

		boolean createNaturals = false;
		File naturals = new File(path + "Naturals.tla");
		if (!naturals.exists()) {
			createNaturals = true;
			try {
				naturals.createNewFile();
				Writer fw = new FileWriter(naturals);
				String n;
				n = naturals();
				fw.write(n);
				fw.close();

			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		boolean createIntegers = false;
		File integers = new File(path + "Integers.tla");
		if (!integers.exists()) {
			createIntegers = true;
			try {
				integers.createNewFile();
				Writer fw = new FileWriter(integers);
				String n;
				n = integers();
				fw.write(n);
				fw.close();

			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		boolean createFiniteSets = false;
		File finiteSets = new File(path + "FiniteSets.tla");
		if (!finiteSets.exists()) {
			createFiniteSets = true;
			try {
				finiteSets.createNewFile();
				Writer fw = new FileWriter(finiteSets);
				String n;
				n = finiteSets();
				fw.write(n);
				fw.close();

			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		boolean createSequences = false;
		File sequences = new File(path + "Sequences.tla");
		if (!sequences.exists()) {
			createSequences = true;
			try {
				sequences.createNewFile();
				Writer fw = new FileWriter(sequences);
				String n;
				n = sequences();
				fw.write(n);
				fw.close();

			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		StringBuilder s = new StringBuilder();

		File config = new File(name + ".cfg");
		String configName = null;
		if (config.exists()) {
			configName = name;
		}

		try {
			s = Main.start(name, configName, false);
		} catch (FrontEndException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (MyException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		if (createNaturals) {
			naturals.delete();
		}
		if (createIntegers) {
			integers.delete();
		}

		if (createFiniteSets) {
			finiteSets.delete();
		}

		if (createSequences) {
			sequences.delete();
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

	private static String integers() {
		String n = "---- MODULE Integers ----\n" + "EXTENDS Naturals\n"
				+ "Int == { }\n" + "-. a == 0 - a\n" + "====";
		return n;
	}

	private static String naturals() {
		String n = "---- MODULE Naturals ----\n" + "Nat       == { }\n"
				+ "a+b       == {a, b}\n" + "a-b       == {a, b}\n"
				+ "a*b       == {a, b}\n" + "a^b       == {a, b}\n"
				+ "a<b       ==  a = b\n" + "a>b       ==  a = b\n"
				+ "a \\leq b  ==  a = b\n" + "a \\geq b  ==  a = b\n"
				+ "a % b     ==  {a, b}\n" + "a \\div b  ==  {a, b}\n"
				+ "a .. b    ==  {a, b}\n" + "====";
		return n;
	}

	private static String finiteSets() {
		String n = "---- MODULE FiniteSets ----\n" + "IsFiniteSets(S) == S\n"
				+ "Cardinality(S) == S\n" + "====";
		return n;

	}

	private static String sequences() {
		String n = "---- MODULE Sequences ----\n" + "Seq(s) == s\n"
				+ "Len(s) == s\n" + "s \\o t  == s\n" + "Append(s,e) == s\n"
				+ "Head(s) == s\n" + "Tail(s) == s\n" + "SubSeq(s,m,n) == s\n"
				+ "====";
		return n;
	}

}
