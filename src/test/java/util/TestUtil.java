package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class TestUtil {

	public static final String TLA_BEGIN = "----- MODULE Testing -----\n";
	public static final String TLA_END = "============================";

	public static String getTreeAsString(final String testMachine)
			throws BException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);

		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}

	public static String fileToString(String fileName) throws IOException {
		File file = new File(fileName);
		BufferedReader in = new BufferedReader(new FileReader(file));
		StringBuilder sb = new StringBuilder();
		String line;
		boolean first = true;
		while ((line = in.readLine()) != null) {
			if (!first)
				sb.append("\n");
			first = false;
			sb.append(line);
		}
		return sb.toString();
	}
}
