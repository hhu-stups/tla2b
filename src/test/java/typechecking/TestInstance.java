/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package typechecking;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import util.FileUtil;
import util.ToolIO;
import util.TypeCheckerTest;

public class TestInstance {

	private static final char fileseparator = FileUtil.separatorChar;
	private static String path = "src/test/resources/typechecking/modules/";
	static {
		path = path.replace('/', fileseparator);
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.setUserDir(path);
	}
	
	@Test
	public void TestNamedInstance() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS start \n"
				+ "VARIABLES c \n"
				+ "count == INSTANCE Counter WITH x <- c  \n"
				+ "Init == count!Init\n"
				+ "Next == count!Next\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.variables.get("c").toString());
		assertEquals("INTEGER", t.constants.get("start").toString());
	}
	
	
	@Test
	public void TestNamedInstance2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES c \n"
				+ "count == INSTANCE Poly WITH x <- c \n"
				+ "Init == count!foo = 1"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.variables.get("c").toString());
	}
	
	@Test
	public void TestNamedInstance3() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES c \n"
				+ "count == INSTANCE Poly WITH x <- c \n"
				+ "Init == count!bar(1) \n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.variables.get("c").toString());
	}
	
	@Test
	public void TestNamedInstance4() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "VARIABLES c, c2\n"
				+ "count == INSTANCE Poly WITH x <- c \n"
				+ "count2 == INSTANCE Poly WITH x <- c2 \n"
				+ "foo == count!foo = TRUE \n"
				+ "foo2 == count2!foo = 1 \n"
				+ "Init == foo /\\ foo2"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.variables.get("c").toString());
		assertEquals("INTEGER", t.variables.get("c2").toString());
	}
	
	@Test
	public void TestNamedInstance5() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "VARIABLES c \n"
				+ "poly == INSTANCE Poly WITH x <- c \n"
				+ "Init == poly!foo = TRUE \n"
				+ "ASSUME poly!baz(1,k)\n"
				+ "=================================";

		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("BOOL", t.variables.get("c").toString());
		assertEquals("INTEGER", t.constants.get("k").toString());
	}
	
	@Test
	public void TestCon4Con() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS c2, val2 \n"
				+ "INSTANCE Value WITH val <- val2, c <- c2 \n"
				+ "ASSUME def"
				+ "=================================";
		final String config = "CONSTANTS c2 = 1";
		TypeCheckerTest t = new TypeCheckerTest(module, config, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("c2").toString());
		assertEquals("INTEGER", t.constants.get("val2").toString());
	}
	
	@Test
	public void Test2Instances() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "Inst == INSTANCE Value WITH val <- 1, c <- k \n"
				+ "Inst2 == INSTANCE Value WITH val <- TRUE, c <- k2 \n"
				+ "ASSUME Inst!def /\\ Inst2!def"
				+ "=================================";
		TypeCheckerTest t = new TypeCheckerTest(module, null, true);
		t.start();
		assertEquals("INTEGER", t.constants.get("k").toString());
		assertEquals("BOOL", t.constants.get("k2").toString());
	}
	
}
