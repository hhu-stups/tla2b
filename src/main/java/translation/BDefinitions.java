/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;

import tla2sany.semantic.OpDefNode;

public class BDefinitions implements TranslationGlobals {

	private OpDefNode[] input_defs;

	public BDefinitions(OpDefNode[] defs) {
		input_defs = defs;
	}

	public ArrayList<OpDefNode> getBDefinitions() {
		ArrayList<OpDefNode> result = new ArrayList<OpDefNode>();
		for (int i = 0; i < input_defs.length; i++) {
			OpDefNode def = input_defs[i];
			Boolean usedDefintion = (Boolean) def
					.getToolObject(PRINT_DEFINITION);
			if (usedDefintion != null && usedDefintion) {
				ConstantObj conObj = (ConstantObj) def
						.getToolObject(CONSTANT_OBJECT);
				if (conObj != null) {
					if (def.getName().toString().equals(conObj.getValue())) {
						// defname equals modelvalues
						continue;
					}
				}
				result.add(def);
			}
		}
		return result;
	}
}
