package translation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;

import exceptions.ConfigFileErrorException;
import exceptions.FrontEndException;
import exceptions.SemanticErrorException;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;
import types.BType;
import types.IType;
import util.StandardModules;

// contains the content of a tla+ module
public class ModuleContext implements ASTConstants, ToolGlobals,
		TranslationGlobals, IType {
	private final ModuleNode moduleNode;
	protected Hashtable<String, OpDefNode> definitions;

	// Constants which appear in the resulting B machine
	private ArrayList<String> bConstants = new ArrayList<String>();
	protected ArrayList<LetDef> globalLets = new ArrayList<LetDef>();
	protected ArrayList<String> letsNames = new ArrayList<String>();

	protected Hashtable<String, ConstantObj> conObjs;
	protected Hashtable<String, String> overrides;
	protected ArrayList<String> setEnumeration;
	protected ArrayList<String> invariants = new ArrayList<String>();
	protected ArrayList<BOperation> bOperations = new ArrayList<BOperation>();
	protected ArrayList<BInit> inits = new ArrayList<BInit>();
	protected ExprNode next;
	protected ArrayList<String> definitionMacro = new ArrayList<String>();

	private int INSTANCE_SUBSITUTION_ID = 10;
	private ArrayList<OpApplNode> ifThenElseNodes = new ArrayList<OpApplNode>();

	public ModuleContext(ModuleNode rootModule, ConfigTypeChecker ctc)
			throws FrontEndException, ConfigFileErrorException,
			SemanticErrorException {

		// set root Module
		this.moduleNode = rootModule;

		SymbolSorter.sortDeclNodes(moduleNode.getConstantDecls());
		SymbolSorter.sortDeclNodes(moduleNode.getVariableDecls());
		SymbolSorter.sortOpDefNodes(moduleNode.getOpDefs());

		this.definitions = SymbolSorter
				.getDefsHashTable(moduleNode.getOpDefs());

		SpecAnalyser specAnalyser = new SpecAnalyser(ctc.getSpec(),
				ctc.getInit(), ctc.getNext(), this.definitions);
		specAnalyser.start();
		this.inits = specAnalyser.getInits();
		this.next = specAnalyser.getNextExpr();

		if (moduleNode.getVariableDecls().length > 0) {
			if (inits.size() == 0) {
				throw new ConfigFileErrorException(
						"No initialisation predicate in the configuration file");
			}
		}

		findOperations(next, specAnalyser.getNextName());

		overrides = ctc.getOverrides();
		if (ctc.getEnumeratedSet().size() > 0)
			setEnumeration = ctc.getEnumeratedSet();
		bConstants = ctc.getbConstants();
		if (ctc.getInvariants().size() > 0) {
			invariants = ctc.getInvariants();

			for (int i = 0; i < invariants.size(); i++) {
				OpDefNode def = definitions.get(invariants.get(i));
				def.setToolObject(PRINT_DEFINITION, true);
			}
		}

		if (ctc.getConObjs().size() > 0)
			conObjs = ctc.getConObjs();

		startAnalyse();
	}

	public ModuleContext(ModuleNode moduleNode) throws FrontEndException,
			SemanticErrorException, ConfigFileErrorException {
		this.moduleNode = moduleNode;

		SymbolSorter.sortDeclNodes(moduleNode.getConstantDecls());
		SymbolSorter.sortDeclNodes(moduleNode.getVariableDecls());
		SymbolSorter.sortOpDefNodes(moduleNode.getOpDefs());

		this.definitions = SymbolSorter
				.getDefsHashTable(moduleNode.getOpDefs());

		// every TLA+ constant is a B constant
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			bConstants.add(moduleNode.getConstantDecls()[i].getName()
					.toString());
		}

		/*
		 * Conventions: if there is no config file use the 'Next' defintion as
		 * next state relation, 'Init' as initialisation predicate
		 */
		SpecAnalyser specAnalyser = new SpecAnalyser("Spec", "Init", "Next",
				this.definitions);
		specAnalyser.start();
		this.inits = specAnalyser.getInits();
		this.next = specAnalyser.getNextExpr();

		if (moduleNode.getVariableDecls().length > 0) {
			if (inits.size() == 0) {
				throw new ConfigFileErrorException(
						"No initialisation predicate in the configuration file");
			}
		}

		findOperations(next, specAnalyser.getNextName());

		startAnalyse();
	}

	public void startAnalyse() throws ConfigFileErrorException {
		evalUsedDefintions();
		KeywordRenamer keywordRenamer = new KeywordRenamer(moduleNode);
		keywordRenamer.start();
	}

	public ModuleNode getRoot() {
		return moduleNode;
	}

	public ArrayList<String> getInvariants() {
		return invariants;
	}

	public ArrayList<String> getBConstants() {
		ArrayList<String> clone = new ArrayList<String>(bConstants);
		return clone;
	}

	public Hashtable<String, String> getOverrides() {
		return this.overrides;
	}

	public ArrayList<String> getEnum() {
		return setEnumeration;
	}

	// find b operations
	private void findOperations(ExprNode e, String opName)
			throws FrontEndException, ConfigFileErrorException {
		if (e == null)
			return;
		String name = opName;
		ArrayList<OpApplNode> existQuans = new ArrayList<OpApplNode>();
		findOperationsInSemanticNode(e, name, existQuans,
				new LinkedHashMap<String, LetDef>());
	}

	private void findOperationsInSemanticNode(SemanticNode node, String name,
			ArrayList<OpApplNode> existQuans,
			LinkedHashMap<String, LetDef> localDefintions)
			throws FrontEndException, ConfigFileErrorException {
		switch (node.getKind()) {
		case OpApplKind: {
			findOperationsInOpApplNode((OpApplNode) node, name, existQuans,
					localDefintions);
			return;
		}
		case LetInKind: {
			// LetInNode letNode = (LetInNode) node;
			// BOperation op = new BOperation(name, letNode, existQuans);
			// bOperations.add(op);

			LetInNode l = (LetInNode) node;
			LinkedHashMap<String, LetDef> letsList = new LinkedHashMap<String, LetDef>();
			for (int i = 0; i < l.getLets().length; i++) {

				OpDefNode d = l.getLets()[i];
				String letName = createName(d.getName().toString());
				LetDef letDef = new LetDef(letName, d, new ArrayList<String>(),
						new LinkedHashMap<String, LetDef>(letsList));
				globalLets.add(letDef);
				letsList.put(d.getName().toString(), letDef);

				// visit lets to determine used definitions
				ArrayList<String> ps = new ArrayList<String>(getParams(d));
				String prefix = name.substring(0, name.lastIndexOf('!') + 1);
				visitExprNode(d.getBody(), prefix, ps);
			}

			letsList.putAll(localDefintions);
			findOperationsInSemanticNode(l.getBody(), name, existQuans,
					letsList);
			return;
		}
		case SubstInKind: {
			SubstInNode substInNode = (SubstInNode) node;

			BOperation op = new BOperation(name, substInNode, existQuans,
					localDefintions);
			bOperations.add(op);
			// findOperations(substInNode.getBody(), name);
			return;
		}
		case LabelKind:
		default:

			// TODO no valid b operation
			throw new RuntimeException("not implemented");
		}

	}

	private void findOperationsInOpApplNode(OpApplNode n, String name,
			ArrayList<OpApplNode> existQuans,
			LinkedHashMap<String, LetDef> localDefintions)
			throws FrontEndException, ConfigFileErrorException {
		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind
				&& !BBuiltInOPs.contains(n.getOperator().getName())) {
			String defName = n.getOperator().getName().toString();
			String prefix = name.substring(0, name.lastIndexOf('!') + 1);
			OpDefNode def = definitions.get(prefix + defName);
			if (def.getParams().length > 0) {
				def.setToolObject(PRINT_DEFINITION, true);
				BOperation op = new BOperation(def.getName().toString(), n,
						existQuans, localDefintions);
				bOperations.add(op);
				return;
			} else {
				def.setToolObject(PRINT_DEFINITION, false);
				findOperationsInSemanticNode(def.getBody(), def.getName()
						.toString(), existQuans,
						new LinkedHashMap<String, LetDef>());
				return;
			}

		} else if (kind == BuiltInKind) {
			int opcode = BuiltInOPs.getOpCode(n.getOperator().getName());
			switch (opcode) {
			case OPCODE_dl: // DisjList
			{
				if (n.getArgs().length == 1) {
					findOperationsInSemanticNode(n.getArgs()[0], name,
							existQuans, localDefintions);
					return;
				}
				for (int i = 0; i < n.getArgs().length; i++) {
					findOperationsInSemanticNode(n.getArgs()[i],
							name + (i + 1), existQuans, localDefintions);
				}
				return;
			}
			case OPCODE_lor: {
				for (int i = 0; i < n.getArgs().length; i++) {
					findOperationsInSemanticNode(n.getArgs()[i],
							name + (i + 1), existQuans, localDefintions);
				}
				return;
			}
			case OPCODE_be: { // BoundedExists
				ArrayList<OpApplNode> clone = new ArrayList<OpApplNode>(
						existQuans);
				clone.add(n);
				findOperationsInSemanticNode(n.getArgs()[0], name, clone,
						localDefintions);
				return;
			}

			case OPCODE_unchanged:
			case OPCODE_eq: // =
			case OPCODE_noteq: // /=, #
			case OPCODE_neg: // Negation
			case OPCODE_lnot: // Negation
			case OPCODE_cl: // $ConjList
			case OPCODE_land: // \land
			case OPCODE_equiv: // \equiv
			case OPCODE_implies: // =>
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_in: // \in
			case OPCODE_notin: // \notin
			case OPCODE_subseteq: // \subseteq - subset or equal
			case OPCODE_fa: // $FcnApply f[1]
			case OPCODE_ite: // IF THEN ELSE
			case OPCODE_case: {
				BOperation op = new BOperation(name, n, existQuans,
						localDefintions);
				bOperations.add(op);
				return;
			}
			}
		}
		throw new FrontEndException(String.format(
				"Expected an action at '%s' :\n%s", n.getOperator().getName()
						.toString(), n.getLocation().toString()));

	}

	private ArrayList<String> getParams(OpDefNode def) {
		ArrayList<String> res = new ArrayList<String>();
		for (int i = 0; i < def.getParams().length; i++) {
			res.add(def.getParams()[i].getName().toString());
		}
		return res;
	}

	/**
	 * @throws ConfigFileErrorException
	 * 
	 */
	// TODO find local definitions
	private void evalUsedDefintions() throws ConfigFileErrorException {
		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			visitExprNode(assumes[i].getAssume(), "", new ArrayList<String>());
		}

		for (int i = 0; i < inits.size(); i++) {
			BInit bInit = inits.get(i);
			visitExprNode(bInit.getNode(), bInit.getPrefix(),
					new ArrayList<String>());
		}

		for (int i = 0; i < bOperations.size(); i++) {
			BOperation op = bOperations.get(i);
			String name = op.getName();
			String prefix = name.substring(0, name.lastIndexOf('!') + 1);
			ArrayList<String> ps = new ArrayList<String>();
			for (int j = 0; j < op.getExistQuans().size(); j++) {
				OpApplNode node = op.getExistQuans().get(j);
				ExprNode[] in = node.getBdedQuantBounds();
				for (int k = 0; k < in.length; k++) {
					visitExprNode(in[k], prefix, new ArrayList<String>());
				}
				ps.addAll(op.getOpParams());
			}
			visitExprNode(bOperations.get(i).getNode(), prefix, ps);
		}

		for (int i = 0; i < invariants.size(); i++) {
			String invName = invariants.get(i);
			OpDefNode def = definitions.get(invName);
			def.setToolObject(PRINT_DEFINITION, true);
			String newPrefix = invName.substring(0,
					invName.lastIndexOf('!') + 1);
			visitExprNode(def.getBody(), newPrefix, new ArrayList<String>());
		}

		if (overrides != null) {
			for (Iterator<String> i = overrides.values().iterator(); i
					.hasNext();) {
				String defName = i.next();
				OpDefNode def = definitions.get(defName);
				def.setToolObject(PRINT_DEFINITION, true);
				String newPrefix = defName.substring(0,
						defName.lastIndexOf('!') + 1);
				visitExprNode(def.getBody(), newPrefix, new ArrayList<String>());
			}
		}

	}

	/**
	 * @param exprOrOpArgNode
	 * @throws ConfigFileErrorException
	 */
	private void visitExprOrOpArgNode(ExprOrOpArgNode n, String prefix,
			ArrayList<String> parameters) throws ConfigFileErrorException {
		if (n instanceof ExprNode) {
			visitExprNode((ExprNode) n, prefix, new ArrayList<String>(
					parameters));
		} else if (n instanceof OpArgNode) {
			OpArgNode opArgNode = (OpArgNode) n;
			SymbolNode s = opArgNode.getOp();

			ExprOrOpArgNode e = (ExprOrOpArgNode) s
					.getToolObject(INSTANCE_SUBSITUTION_ID);
			if (e != null) {
				visitExprOrOpArgNode(e, Util.getPrefixWithoutLast(prefix),
						new ArrayList<String>(parameters));
				return;
			}

			String overrideName = (String) s
					.getToolObject(OVERRIDE_SUBSTITUTION_ID);
			if (overrideName != null) {
				OpDefNode def = definitions.get(overrideName);
				if (!StandardModules.contains(def
						.getOriginallyDefinedInModuleNode().getName()
						.toString())
						&& !StandardModules.contains(def.getSource()
								.getOriginallyDefinedInModuleNode().getName()
								.toString())) {
					def.setToolObject(PRINT_DEFINITION, true);
				}

				return;
			}

			if (s instanceof OpDefNode) {
				s.setToolObject(PRINT_DEFINITION, true);
				visitExprNode(((OpDefNode) s).getBody(),
						Util.getPrefixWithoutLast(prefix),
						new ArrayList<String>());
				return;
			}

			throw new ConfigFileErrorException(
					String.format(
							"Operator '%s' has %s arguments and must be overriden in the configuration file.",
							s.getName(), s.getArity()));
		}
	}

	private void visitExprNode(ExprNode node, String prefix,
			ArrayList<String> parameters) throws ConfigFileErrorException {
		switch (node.getKind()) {
		case OpApplKind: {
			visitOpApplNode((OpApplNode) node, prefix, new ArrayList<String>(
					parameters));
			return;
		}
		case LetInKind: {
			LetInNode l = (LetInNode) node;
			for (int i = 0; i < l.getLets().length; i++) {
				OpDefNode d = l.getLets()[i];
				d.setToolObject(LET_PARAMS_ID,
						new ArrayList<String>(parameters));

				// visit lets to determine used definitions
				ArrayList<String> ps = new ArrayList<String>();
				ps.addAll(parameters);
				ps.addAll(getParams(d));
				visitExprNode(d.getBody(), prefix, ps);
			}
			visitExprNode(l.getBody(), prefix,
					new ArrayList<String>(parameters));
			return;
		}
		case SubstInKind: {
			SubstInNode substInNode = (SubstInNode) node;
			Subst[] substs = substInNode.getSubsts();
			for (int i = 0; i < substs.length; i++) {
				OpDeclNode op = substs[i].getOp();
				op.setToolObject(INSTANCE_SUBSITUTION_ID, substs[i].getExpr());
				// System.out.println(substs[i].getExpr().toString(2));
				// visitExprOrOpArgNode(substs[i].getExpr(), prefix,
				// new ArrayList<String>(parameters));
			}
			visitExprNode(substInNode.getBody(), prefix, new ArrayList<String>(
					parameters));
			return;
		}
		}
	}

	/**
	 * @param node
	 * @throws ConfigFileErrorException
	 */
	private void visitOpApplNode(OpApplNode node, String prefix,
			ArrayList<String> parameters) throws ConfigFileErrorException {
		switch (node.getOperator().getKind()) {

		case ConstantDeclKind: {
			for (int i = 0; i < node.getArgs().length; i++) {
				visitExprOrOpArgNode(node.getArgs()[i], prefix, parameters);
			}

			ExprOrOpArgNode e = (ExprOrOpArgNode) node.getOperator()
					.getToolObject(INSTANCE_SUBSITUTION_ID);
			if (e != null) {
				visitExprOrOpArgNode(e, Util.getPrefixWithoutLast(prefix),
						new ArrayList<String>(parameters));
				return;
			}

			String overrideName = (String) node.getOperator().getToolObject(
					OVERRIDE_SUBSTITUTION_ID);
			if (overrideName != null) {
				OpDefNode def = definitions.get(overrideName);
				if (!StandardModules.contains(def
						.getOriginallyDefinedInModuleNode().getName()
						.toString())
						&& !StandardModules.contains(def.getSource()
								.getOriginallyDefinedInModuleNode().getName()
								.toString())) {
					def.setToolObject(PRINT_DEFINITION, true);
				}
				return;
			}

			if (node.getArgs().length > 0) {
				throw new ConfigFileErrorException(
						String.format(
								"Constant '%s' must be overriden in the configuration file.",
								node.getOperator().getName()));
			}

			// normal constant, no substitution and no arguments
			return;
		}

		case VariableDeclKind: {

			return;
		}

		case BuiltInKind: {
			visitBuiltInKind(node, prefix, new ArrayList<String>(parameters));
			return;
		}

		case UserDefinedOpKind: {
			OpDefNode def;
			if (node.getOperator().getToolObject(DEF_OBJECT) != null) {
				def = (OpDefNode) node.getOperator().getToolObject(DEF_OBJECT);
			} else {
				def = (OpDefNode) node.getOperator();
			}

			if (BBuiltInOPs.contains(def.getName())) {
				visitBuiltInKind(node, prefix,
						new ArrayList<String>(parameters));
				return;
			}

			String defName;
			String name = def.getName().toString();
			if (def.getName().toString().toString().startsWith(prefix)) {
				defName = def.getName().toString();
			} else {
				defName = prefix + def.getName().toString();
			}

			String newPrefix = defName.substring(0,
					defName.lastIndexOf('!') + 1);

			// let
			if (!this.definitions.containsKey(defName)) {
				if (this.definitions.containsKey(name)) {
					defName = name;
				} else {
					OpDefNode def2 = (OpDefNode) node.getOperator();
					visitExprNode(def2.getBody(), newPrefix,
							new ArrayList<String>(parameters));
					return;
				}
			}
			// def2 is the instanced definition if there is one
			OpDefNode def2 = definitions.get(defName);
			Boolean b = (Boolean) def2.getToolObject(PRINT_DEFINITION);
			if (b == null || b == true) {
				def2.setToolObject(PRINT_DEFINITION, true);
				visitExprNode(def2.getBody(), newPrefix, getParams(def));
			}

			for (int i = 0; i < node.getArgs().length; i++) {
				visitExprOrOpArgNode(node.getArgs()[i], prefix,
						new ArrayList<String>(parameters));
			}
			return;
		}

		}

	}

	protected String createName(String name) {
		String res = name;
		for (int i = 1; letsNames.contains(res); i++) {
			res = name + i;
		}
		letsNames.add(res);
		return res;
	}

	/**
	 * @param node
	 * @throws ConfigFileErrorException
	 */
	private void visitBuiltInKind(OpApplNode node, String prefix,
			ArrayList<String> parameters) throws ConfigFileErrorException {
		switch (BuiltInOPs.getOpCode(node.getOperator().getName())) {

		case OPCODE_be:
		case OPCODE_bf:
		case OPCODE_soa:
		case OPCODE_sso:
		case OPCODE_nrfs:
		case OPCODE_fc: {
			ExprNode[] in = node.getBdedQuantBounds();
			for (int i = 0; i < in.length; i++) {
				visitExprNode(in[i], prefix, parameters);
			}
			visitExprOrOpArgNode(node.getArgs()[0], prefix, parameters);
			return;
		}
		case OPCODE_ite: {
			ifThenElseNodes.add(node);
			// if(!definitionMacro.contains(IF_THEN_ELSE)){
			// definitionMacro.add(IF_THEN_ELSE);
			// }
			break;
		}

		case OPCODE_bc: {
			if (!definitionMacro.contains(CHOOSE)) {
				definitionMacro.add(CHOOSE);
			}
			break;
		}
		case OPCODE_unchanged: {
			return;
		}
		}
		for (int i = 0; i < node.getArgs().length; i++) {
			visitExprOrOpArgNode(node.getArgs()[i], prefix,
					new ArrayList<String>(parameters));
		}
	}

	public void evalIfThenElse() {
		boolean b = false;
		for (int i = 0; i < ifThenElseNodes.size() && !b; i++) {
			OpApplNode node = ifThenElseNodes.get(i);
			BType t = (BType) node.getToolObject(TYPE_ID);
			if (t.getKind() != BOOL)
				b = true;
		}
		if (b)
			definitionMacro.add(IF_THEN_ELSE);
	}

}
