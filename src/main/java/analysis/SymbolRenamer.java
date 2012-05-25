/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package analysis;

import global.TranslationGlobals;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;


import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;

public class SymbolRenamer implements TranslationGlobals {

	private final static Set<String> KEYWORDS = new HashSet<String>();
	static {
		KEYWORDS.add("seq");
		KEYWORDS.add("left");
		KEYWORDS.add("right");
		KEYWORDS.add("max");
		KEYWORDS.add("min");
		KEYWORDS.add("succ");
		KEYWORDS.add("pred");
		KEYWORDS.add("dom");
		KEYWORDS.add("ran");
		KEYWORDS.add("fnc");
		KEYWORDS.add("rel");
		KEYWORDS.add("id");
		KEYWORDS.add("card");
		KEYWORDS.add("POW");
		KEYWORDS.add("POW1");
		KEYWORDS.add("FIN");
		KEYWORDS.add("FIN1");
		KEYWORDS.add("size");
		KEYWORDS.add("rev");
		KEYWORDS.add("first");
		KEYWORDS.add("last");
		KEYWORDS.add("front");
		KEYWORDS.add("tail");
		KEYWORDS.add("conc");
		KEYWORDS.add("struct");
		KEYWORDS.add("rec");
		KEYWORDS.add("tree");
		KEYWORDS.add("btree");
		KEYWORDS.add("skip");
		KEYWORDS.add("ANY");
		KEYWORDS.add("WHERE");
		KEYWORDS.add("END");
		KEYWORDS.add("BE");
		KEYWORDS.add("VAR");
		KEYWORDS.add("ASSERT");
		KEYWORDS.add("CHOICE");
		KEYWORDS.add("OR");
		KEYWORDS.add("SELECT");
		KEYWORDS.add("EITHER");
		KEYWORDS.add("WHEN");
		KEYWORDS.add("BEGIN");
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("REFINEMENT");
		KEYWORDS.add("IMPLEMENTATION");
		KEYWORDS.add("SETS");
		KEYWORDS.add("CONSTRAINTS");
		KEYWORDS.add("MODEL");
		KEYWORDS.add("SYSTEM");
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("EVENTS");
		KEYWORDS.add("OPERATIONS");
	}

	private final static Hashtable<String, String> INFIX_OPERATOR= new Hashtable<String, String>();
	static {
		INFIX_OPERATOR.put("!!", "ii");
		INFIX_OPERATOR.put("??", "SS");
		INFIX_OPERATOR.put("&", "ii");
	}
	
	private ModuleNode moduleNode;
	private Set<OpDefNode> usedDefinitions;

	private Set<String> newNames = new HashSet<String>();

	/**
	 * @param moduleNode2
	 * @param specAnalyser
	 */
	public SymbolRenamer(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.usedDefinitions = specAnalyser.getUsedDefinitions();
	}
	
	public SymbolRenamer(ModuleNode moduleNode){
		this.moduleNode = moduleNode;
		usedDefinitions = new HashSet<OpDefNode>();
		OpDefNode[] defs = moduleNode.getOpDefs();
		usedDefinitions.add(defs[defs.length-1]);
	}

	public void start() {
		// Variables
		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode v = moduleNode.getVariableDecls()[i];
			String newName = incName(v.getName().toString());
			newNames.add(newName);
			v.setToolObject(NEW_NAME, newName);
		}

		// constants
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode c = moduleNode.getConstantDecls()[i];
			String newName = incName(c.getName().toString());
			newNames.add(newName);
			c.setToolObject(NEW_NAME, newName);
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];

			if (usedDefinitions.contains(def)) {
				evalDefName(def);
				
				
			}
		}

	}

	private void evalDefName(SymbolNode n) {
		String name = n.getName().toString();
		String validName = createValidName(name);
		String newName = incName(validName);
		newNames.add(newName);
		n.setToolObject(NEW_NAME, newName);
	}

	private String createValidName(String s) {
		String newName = s;
		if (newName.contains("!")) {
			newName = newName.replace('!', '_');
		}
		if (newName.startsWith("\\")) {
			newName = newName.substring(1);
		}
		return newName;
	}

	private Boolean existingName(String name) {
		if (newNames.contains(name) || KEYWORDS.contains(name)) {
			return true;
		} else
			return false;
	}

	private String incName(String name) {
		String res = name;
		for (int i = 1; existingName(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	private String incName(String name, ArrayList<String> tempList) {
		String res = name;
		for (int i = 1; existingName(res) || tempList.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}
}
