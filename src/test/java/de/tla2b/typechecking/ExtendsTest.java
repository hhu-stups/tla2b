/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.Util;


public class ExtendsTest {

	@Test
	public void TestExtendsCounter() throws Exception {
		String path = "src/test/resources/typechecking/modules/";
		TestTypeChecker t = Util.typeCheck(path + "ExtendsCounter.tla");
		assertEquals("INTEGER", t.getVariableType("x"));
		assertEquals("INTEGER", t.getConstantType("start"));
	}
}
