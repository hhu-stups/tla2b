/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.config;

import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.TLAType;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.NumeralNode;
import tla2sany.st.TreeNode;
import tlc2.value.Value;

public class TLCValueNode extends NumeralNode implements TranslationGlobals {

	private Value value;
	private TLAType type;

	/**
	 * @param kind
	 * @param stn
	 * @throws AbortException 
	 */
	public TLCValueNode(ValueObj valObj, TreeNode stn) throws AbortException {
		super("1337", stn);
		this.value = valObj.getValue();
		this.type = valObj.getType();
	}

	public String toString2() {
		return "\n*TLCValueNode: Value: '"
				+ value.toString() + "'";
				
	}

	public TLAType getType() {
		return type;
	}

	public Value getValue() {
		return value;
	}
}
