/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;

import de.tla2b.exceptions.NotImplementedException;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.BuiltInOPs;

public class RecursiveFunktion extends BuiltInOPs{

	private OpDefNode def;
	private OpApplNode rfs;
	private OpApplNode ifThenElse;

	public RecursiveFunktion(OpDefNode n, OpApplNode rfs) throws NotImplementedException {
		def = n;
		this.rfs = rfs;
		evalDef();
	}

	/**
	 * @throws NotImplementedException
	 * 
	 */
	private void evalDef() throws NotImplementedException {
		ExprOrOpArgNode e = rfs.getArgs()[0];

		if (e instanceof OpApplNode) {
			OpApplNode o = (OpApplNode) e;
			switch (getOpCode(o.getOperator().getName()))
			{
			case OPCODE_ite:{ // IF THEN ELSE
				ifThenElse = o;
				return;
			}
			}
			throw new NotImplementedException(
					"Only IF/THEN/ELSE or CASE constructs are supported at the body of a recursive function.");
		} else {
			throw new NotImplementedException(
					"Only IF/THEN/ELSE or CASE constructs are supported at the body of a recursive function.");
		}
	}
	
	public OpDefNode getOpDefNode(){
		return def;
	}
	
	public OpApplNode getRF(){
		return rfs;
	}
	
	public OpApplNode getIfThenElse(){
		return ifThenElse;
	}
}
