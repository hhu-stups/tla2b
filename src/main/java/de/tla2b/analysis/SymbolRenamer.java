/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;


import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.BuiltInOPs;

public class SymbolRenamer extends BuiltInOPs implements TranslationGlobals,
		ASTConstants {

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

	private final static Hashtable<String, String> INFIX_OPERATOR = new Hashtable<String, String>();
	static {
		INFIX_OPERATOR.put("!!", "exclamationmark2");
		INFIX_OPERATOR.put("??", "questionmark2");
		INFIX_OPERATOR.put("&", "ampersand1");
		INFIX_OPERATOR.put("&&", "ampersand2");
		INFIX_OPERATOR.put("@@", "at2");
		INFIX_OPERATOR.put("++", "plus2");
		INFIX_OPERATOR.put("--", "minus2");
		INFIX_OPERATOR.put("^", "circumflex1");
		INFIX_OPERATOR.put("^^", "circumflex2");
		INFIX_OPERATOR.put("##", "hash2");
		INFIX_OPERATOR.put("%%", "percent2");
		INFIX_OPERATOR.put("$", "dollar1");
		INFIX_OPERATOR.put("$$", "dollar2");
		INFIX_OPERATOR.put("|", "pipe1");
		INFIX_OPERATOR.put("||", "pipe2");
		INFIX_OPERATOR.put("//", "slash2");
		INFIX_OPERATOR.put("**", "mult2");
		INFIX_OPERATOR.put("...", "dot3");
	}

	private final static Hashtable<String, String> BBUILTIN_OPERATOR = new Hashtable<String, String>();
	static {
		BBUILTIN_OPERATOR.put("+", "plus");
		BBUILTIN_OPERATOR.put("-", "minus");
		BBUILTIN_OPERATOR.put("*", "mult");
		BBUILTIN_OPERATOR.put("^", "power");
		BBUILTIN_OPERATOR.put("<", "lt");
		BBUILTIN_OPERATOR.put(">", "gt");
		BBUILTIN_OPERATOR.put("\\leq", "leq");
		BBUILTIN_OPERATOR.put("\\geq", "geq");
		BBUILTIN_OPERATOR.put("%", "modulo");
		BBUILTIN_OPERATOR.put("\\div", "div");
		BBUILTIN_OPERATOR.put("..", "dot2");
	}

	private ModuleNode moduleNode;
	private Set<OpDefNode> usedDefinitions;

	private Set<String> globalNames = new HashSet<String>();
	private Hashtable<OpDefNode, Set<String>> usedNamesTable = new Hashtable<OpDefNode, Set<String>>();

	/**
	 * @param moduleNode2
	 * @param specAnalyser
	 */
	public SymbolRenamer(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.usedDefinitions = specAnalyser.getUsedDefinitions();
	}

	public SymbolRenamer(ModuleNode moduleNode) {
		this.moduleNode = moduleNode;
		usedDefinitions = new HashSet<OpDefNode>();
		OpDefNode[] defs = moduleNode.getOpDefs();
		usedDefinitions.add(defs[defs.length - 1]);
	}

	public void start() {
		// Variables
		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode v = moduleNode.getVariableDecls()[i];
			String newName = incName(v.getName().toString());
			globalNames.add(newName);
			v.setToolObject(NEW_NAME, newName);
		}

		// constants
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode c = moduleNode.getConstantDecls()[i];
			String newName = incName(c.getName().toString());
			globalNames.add(newName);
			c.setToolObject(NEW_NAME, newName);
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			String newName = getOperatorName(def);
			globalNames.add(newName);
			def.setToolObject(NEW_NAME, newName);
			usedNamesTable.put(def, new HashSet<String>());
		}

		for (int i = 0; i < moduleNode.getAssumptions().length; i++) {
			AssumeNode assumeNode = moduleNode.getAssumptions()[i];
			visitNode(assumeNode.getAssume(), new HashSet<String>());
		}

		for (int i = moduleNode.getOpDefs().length - 1; i >= 0; i--) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			Set<String> usedNames = usedNamesTable.get(def);
			for (int j = 0; j < def.getParams().length; j++) {
				FormalParamNode p = def.getParams()[j];
				String paramName = p.getName().toString();
				String newParamName = incName(paramName);
				p.setToolObject(NEW_NAME, newParamName);
				//Parameter of different definitions calling each other can have the same name
				//usedNames.add(newParamName);
			}
			visitNode(def.getBody(), usedNames);
		}

	}

	private void visitNode(SemanticNode n, Set<String> usedNames) {
		// System.out.println(n.toString(1)+ " "+ n.getKind());

		switch (n.getKind()) {

		case LetInKind: {
			LetInNode letInNode = (LetInNode) n;
			OpDefNode[] defs = letInNode.getLets();

			// Initialize all local definitions (get a new name, get an empty
			// list)
			for (int i = 0; i < defs.length; i++) {
				OpDefNode def = defs[i];
				String newName = getOperatorName(def);
				globalNames.add(newName);
				def.setToolObject(NEW_NAME, newName);
				usedNamesTable.put(def, new HashSet<String>(usedNames));
			}

			// first visit the IN expression
			visitNode(letInNode.getBody(), usedNames);

			// visit the definition itself
			for (int i = defs.length - 1; i >= 0; i--) {
				OpDefNode def = defs[i];
				Set<String> usedNamesOfDef = usedNamesTable.get(def);
				for (int j = 0; j < def.getParams().length; j++) {
					FormalParamNode p = def.getParams()[j];
					String paramName = p.getName().toString();
					String newParamName = incName(paramName);
					p.setToolObject(NEW_NAME, newParamName);
					//usedNamesOfDef.add(newParamName);
				}
				visitNode(def.getBody(), usedNamesOfDef);
			}
			return;
		}

		case OpApplKind: {
			OpApplNode opApplNode = (OpApplNode) n;
			switch (opApplNode.getOperator().getKind()) {

			case BuiltInKind: {
				visitBuiltinNode(opApplNode, usedNames);
				return;
			}

			case UserDefinedOpKind: {
				OpDefNode def = (OpDefNode) opApplNode.getOperator();
				if (BBuiltInOPs.contains(def.getName())) {
					break;
				}

				usedNamesTable.get(def).addAll(usedNames);
				for (int i = 0; i < n.getChildren().length; i++) {
					visitNode(opApplNode.getArgs()[i], usedNames);
				}
				return;
			}
			}

			for (int i = 0; i < opApplNode.getArgs().length; i++) {
				visitNode(opApplNode.getArgs()[i], usedNames);
			}
			return;
		}
		}

		if (n.getChildren() != null) {
			for (int i = 0; i < n.getChildren().length; i++) {
				visitNode(n.getChildren()[i], usedNames);
			}
		}
	}

	private void visitBuiltinNode(OpApplNode opApplNode, Set<String> usedNames) {

		switch (getOpCode(opApplNode.getOperator().getName())) {

		case OPCODE_nrfs:
		case OPCODE_fc: // Represents [x \in S |-> e]
		case OPCODE_bc: // CHOOSE x \in S: P
		case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
		case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
		case OPCODE_bf: // \A x \in S : P
		case OPCODE_be: // \E x \in S : P
		{
			FormalParamNode[][] params = opApplNode.getBdedQuantSymbolLists();
			Set<String> newUsedNames = new HashSet<String>(usedNames);
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode param = params[i][j];
					String paramName = param.getName().toString();
					String newName = incName(paramName, usedNames);
					param.setToolObject(NEW_NAME, newName);
					newUsedNames.add(newName);
				}
			}
			for (int i = 0; i < opApplNode.getBdedQuantBounds().length; i++) {
				visitNode(opApplNode.getBdedQuantBounds()[i], usedNames);
			}

			visitNode(opApplNode.getArgs()[0], newUsedNames);

			return;
		}

		default:
			for (int i = 0; i < opApplNode.getArgs().length; i++) {
				if (opApplNode.getArgs()[i] != null) {
					visitNode(opApplNode.getArgs()[i], usedNames);
				}
			}

		}
	}

	private String getOperatorName(OpDefNode def) {
		String newName = def.getName().toString();

		if (BBUILTIN_OPERATOR.containsKey(newName)) {
			// a B built-in operator is defined outside of a standard module
			if (!STANDARD_MODULES.contains(def.getSource()
					.getOriginallyDefinedInModuleNode().getName().toString())) {
				return incName(BBUILTIN_OPERATOR.get(newName));
			}
		}

		// replace invalid infix operator names
		for (String e : INFIX_OPERATOR.keySet()) {
			if (newName.contains(e)) {
				newName = newName.replace(e, INFIX_OPERATOR.get(e));
			}
		}

		// replace exclamation marks
		if (newName.contains("!")) {
			newName = newName.replace('!', '_');
		}

		// replace slashes
		if (newName.contains("\\")) {
			newName = newName.replace("\\", "");
		}

		return incName(newName);
	}

	private Boolean existingName(String name) {
		if (globalNames.contains(name) || KEYWORDS.contains(name)) {
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

	private String incName(String name, Set<String> tempSet) {
		String res = name;
		for (int i = 1; existingName(res) || tempSet.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}
}
