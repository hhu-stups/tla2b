/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package prettyprintb;

import static org.junit.Assert.assertEquals;
import static util.TestUtil.getTreeAsString;

import org.junit.Ignore;
import org.junit.Test;

import translation.Main;
import util.ToolIO;

public class TestPredicateVsBoolValue {

	@Ignore
	@Test
	public void testInstance() throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		String module = "---- MODULE Testing----\n"
				+ "foo == TRUE \n"
				+ "ASSUME foo \n"
				+ "=======";
		StringBuilder sb = Main.start(module, null, true);
		System.out.println(sb);
		//TODO
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES foo \n"
				+ "DEFINITIONS foo == TRUE\n"
				+ "END";
		assertEquals(getTreeAsString(expected), getTreeAsString(sb.toString()));
	}
}
