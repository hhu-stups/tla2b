/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.typechecking;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;

import util.ToolIO;

public class TypeConflictsTest {

	@Test(expected = TypeErrorException.class)
	public void testTypeConflict1() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = {k} \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testTypeConflict2() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME {k} = k  \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
	
	@Test(expected = TypeErrorException.class)
	public void testTypeConflict3() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME {{k}} = k  \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
	
	@Test(expected = TypeErrorException.class)
	public void testTypeConflict4() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> k]  \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
	
	@Test(expected = TypeErrorException.class)
	public void testTypeConflict5() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x \\in {} |-> k]  \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
	
	@Test(expected = TypeErrorException.class)
	public void testTypeConflict6() throws FrontEndException, TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a,b \n"
				+ "ASSUME a = [x|->1] /\\ b = [y|->a, x|->1] /\\ a=b  \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
}
