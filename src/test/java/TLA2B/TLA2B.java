/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package TLA2B;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.Test;

import util.FileUtil;
import util.ToolIO;

public class TLA2B {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/prettyprint/realworld/";
	private static String name;
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}

	@Test
	public void testQueens() throws Exception {
		ToolIO.reset();
		name = "Queens";
		File machine = new File(path + name + "_tla.mch");
		if(machine.exists()){
			machine.delete();
		}
		translation.TLA2B.main(new String[] { path + name + ".tla" });
		assertTrue(machine.exists());
		machine.delete();
	}
}
