package util;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Start;

public class TestUtil {

	public static final String TLA_BEGIN = "----- MODULE Testing -----\n";
	public static final String TLA_END = "============================";
	
	
	public static  String getTreeAsString(final String testMachine) throws BException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);

		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}
}
