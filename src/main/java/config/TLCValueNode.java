/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package config;

import global.TranslationGlobals;
import tla2sany.semantic.ExprNode;
import tla2sany.st.TreeNode;
import tlc2.value.Value;
import types.BType;

public class TLCValueNode extends ExprNode implements TranslationGlobals {

	private Value value;
	private BType type;

	/**
	 * @param kind
	 * @param stn
	 */
	public TLCValueNode(ValueObj valObj, TreeNode stn) {
		super(TLCValueKind, stn);
		this.value = valObj.getValue();
		this.type = valObj.getType();
	}

	public final String toString(int depth) {
		if (depth <= 0)
			return "";
		return "\n*TLCValueNode: Value: '"
				+ value.toString() + "'";
				
	}

	public BType getType() {
		return type;
	}

	public Value getValue() {
		return value;
	}
}
