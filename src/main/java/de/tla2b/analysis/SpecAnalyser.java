/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.SemanticErrorException;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.IType;
import de.tla2b.types.TLAType;




import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class SpecAnalyser extends BuiltInOPs implements ASTConstants,
		ToolGlobals, IType, TranslationGlobals {
	private OpDefNode spec;
	private OpDefNode init;
	private OpDefNode next;
	private ArrayList<OpDefNode> invariants;

	private ModuleNode moduleNode;
	private ExprNode nextExpr;
	private String nextName;
	private ArrayList<OpDeclNode> bConstants;
	// used to check if a b constant has arguments and is not overriden in the
	// configfile

	private ArrayList<BOperation> bOperations;
	private ArrayList<ExprNode> inits;
	private ArrayList<LetInNode> globalLets = new ArrayList<LetInNode>();
	// these local definitions occur in assume nodes or in BOperations and will
	// be added in the front part of the definitions clause of the resulting B
	// Machine

	private ArrayList<OpApplNode> ifThenElseNodes = new ArrayList<OpApplNode>();

	private Set<OpDefNode> bDefinitionsSet = new HashSet<OpDefNode>();
	// set of OpDefNodes which will appear in the resulting B Machine
	private Set<OpDefNode> usedDefinitions = new HashSet<OpDefNode>();
	// definitions which are used for the type inference algorithm
	private Hashtable<OpDefNode, FormalParamNode[]> letParams = new Hashtable<OpDefNode, FormalParamNode[]>();
	// additional parameters of an let Operator, these parameters are from the
	// surrounding operator
	private ArrayList<String> definitionMacros = new ArrayList<String>();

	private ArrayList<RecursiveFunktion> recursiveFunctions = new ArrayList<RecursiveFunktion>();

	/**
	 * @param m
	 * @param conEval
	 */
	public SpecAnalyser(ModuleNode m, ConfigfileEvaluator conEval) {
		this.moduleNode = m;
		this.spec = conEval.getSpecNode();
		this.init = conEval.getInitNode();
		this.next = conEval.getNextNode();
		this.invariants = conEval.getInvariants();
		this.bConstants = conEval.getbConstantList();
	}

	public SpecAnalyser(ModuleNode m) {
		this.moduleNode = m;
		Hashtable<String, OpDefNode> definitions = new Hashtable<String, OpDefNode>();
		for (int i = 0; i < m.getOpDefs().length; i++) {
			definitions.put(m.getOpDefs()[i].getName().toString(),
					m.getOpDefs()[i]);
		}
		this.spec = definitions.get("Spec");
		this.init = definitions.get("Init");
		this.next = definitions.get("Next");

		// TODO are constant in the right order
		this.bConstants = new ArrayList<OpDeclNode>();
		this.bConstants.addAll(Arrays.asList(m.getConstantDecls()));
	}

	public void start() throws SemanticErrorException, FrontEndException,
			ConfigFileErrorException, NotImplementedException {
		if (spec != null) {
			evalSpec();
		} else {
			evalInit();
			evalNext();
		}
		findOperations();

		findDefinitions();
		usedDefinitions.addAll(bDefinitionsSet);

		// test whether there is a init predicate if there is a variable
		if (moduleNode.getVariableDecls().length > 0 && inits == null) {
			throw new SemanticErrorException("No initial predicate is defined.");
		}

		// check if there is B constant with arguments.
		for (int i = 0; i < bConstants.size(); i++) {
			OpDeclNode con = bConstants.get(i);
			if (con.getArity() > 0) {
				throw new ConfigFileErrorException(
						String.format(
								"Constant '%s' must be overriden in the configuration file.",
								con.getName()));
			}
		}

		evalRecursiveFunctions();
	}

	private void evalInit() {
		if (init != null) {
			inits = new ArrayList<ExprNode>();
			inits = new ArrayList<ExprNode>();
			inits.add(init.getBody());
		}
	}

	private void evalNext() throws FrontEndException {
		if (next != null) {
			this.nextExpr = next.getBody();
			this.nextName = next.getName().toString();
		}
	}

	public void evalSpec() throws SemanticErrorException, FrontEndException {
		if (spec != null) {
			inits = new ArrayList<ExprNode>();
			processConfigSpec(spec.getBody());
		}

	}

	private void processConfigSpec(ExprNode exprNode)
			throws SemanticErrorException, FrontEndException {

		if (exprNode instanceof OpApplNode) {
			OpApplNode opApp = (OpApplNode) exprNode;
			ExprOrOpArgNode[] args = opApp.getArgs();
			if (args.length == 0) {
				SymbolNode opNode = opApp.getOperator();
				if (opNode instanceof OpDefNode) {
					OpDefNode def = (OpDefNode) opNode;
					ExprNode body = def.getBody();
					body.levelCheck(1);
					if (body.getLevel() == 1) {
						inits.add(exprNode);
					} else {
						processConfigSpec(body);
					}
					return;
				}
				throw new SemanticErrorException(
						"Can not handle specification conjunction.");
			}

			int opcode = BuiltInOPs.getOpCode(opApp.getOperator().getName());
			if (opcode == OPCODE_cl || opcode == OPCODE_land) {
				for (int i = 0; i < args.length; i++) {
					this.processConfigSpec((ExprNode) args[i]);
				}
				return;
			}

			if (opcode == OPCODE_box) {
				SemanticNode boxArg = args[0];
				if ((boxArg instanceof OpApplNode)
						&& BuiltInOPs.getOpCode(((OpApplNode) boxArg)
								.getOperator().getName()) == OPCODE_sa) {
					ExprNode next = (ExprNode) ((OpApplNode) boxArg).getArgs()[0];
					this.nextExpr = next;
					this.nextName = "Next";
					return;
				}
			}
		}
		if (exprNode.getLevel() <= 1) {
			// init
			inits.add(exprNode);
		} else if (exprNode.getLevel() == 3) {
			// temporal

		} else {
			throw new SemanticErrorException(
					"Can not handle specification conjunction.");
		}

	}

	/**
	 * Searches for BOperations in a ExprNode. BOperations are seperated with
	 * the aid of the disjunction (\/) operator.
	 * 
	 * @param exprNode
	 * @param opName
	 *            the name of the definition where exprNode occur
	 * @throws FrontEndException
	 * @throws ConfigFileErrorException
	 */
	private void findOperations() throws FrontEndException,
			ConfigFileErrorException {
		if (nextExpr == null)
			return;
		bOperations = new ArrayList<BOperation>();
		ArrayList<OpApplNode> existQuans = new ArrayList<OpApplNode>();
		findOperationsInSemanticNode(nextExpr, nextName, existQuans);
	}

	/**
	 * 
	 * @param node
	 * @param opName
	 * @param existQuans
	 *            a list containing all existential quantifier which will be
	 *            parameters in the resulting B Maschine
	 * @throws FrontEndException
	 * @throws ConfigFileErrorException
	 */
	private void findOperationsInSemanticNode(SemanticNode node, String opName,
			ArrayList<OpApplNode> existQuans) throws FrontEndException,
			ConfigFileErrorException {
		switch (node.getKind()) {
		case OpApplKind: {
			findOperationsInOpApplNode((OpApplNode) node, opName, existQuans);
			return;
		}
		case LetInKind: {
			LetInNode letInNode = (LetInNode) node;
			globalLets.add(letInNode);

			findOperationsInSemanticNode(letInNode.getBody(), opName,
					existQuans);
			return;
		}
		case NumeralKind: {
			int val = ((NumeralNode) node).val();
			throw new FrontEndException(String.format(
					"Expected an action at '%s'.\n%s", val, node.getLocation()
							.toString()));
		}

		case StringKind: {
			StringNode s = (StringNode) node;
			throw new FrontEndException(String.format(
					"Expected an action at '\"%s\"'.\n%s", s.getRep(), node
							.getLocation().toString()));
		}

		default:
			throw new FrontEndException(String.format(
					"Expected an action.\n%s", node.getLocation().toString()));
		}

	}

	private void findOperationsInOpApplNode(OpApplNode n, String name,
			ArrayList<OpApplNode> existQuans) throws FrontEndException,
			ConfigFileErrorException {
		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind
				&& !BBuiltInOPs.contains(n.getOperator().getName())) {
			OpDefNode def = (OpDefNode) n.getOperator();
			usedDefinitions.add(def);
			if (def.getParams().length > 0) {
				BOperation op = new BOperation(def.getName().toString(), n,
						existQuans);
				bOperations.add(op);
				return;
			} else {
				findOperationsInSemanticNode(def.getBody(), def.getName()
						.toString(), existQuans);
				return;
			}

		} else if (kind == BuiltInKind) {
			int opcode = BuiltInOPs.getOpCode(n.getOperator().getName());
			switch (opcode) {
			case OPCODE_dl: // DisjList
			{
				if (n.getArgs().length == 1) {
					findOperationsInSemanticNode(n.getArgs()[0], name,
							existQuans);
					return;
				}
				for (int i = 0; i < n.getArgs().length; i++) {
					findOperationsInSemanticNode(n.getArgs()[i],
							name + (i + 1), existQuans);
				}
				return;
			}
			case OPCODE_lor: {
				for (int i = 0; i < n.getArgs().length; i++) {
					findOperationsInSemanticNode(n.getArgs()[i],
							name + (i + 1), existQuans);
				}
				return;
			}
			case OPCODE_be: { // BoundedExists
				ArrayList<OpApplNode> clone = new ArrayList<OpApplNode>(
						existQuans);
				clone.add(n);
				findOperationsInSemanticNode(n.getArgs()[0], name, clone);
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
				BOperation op = new BOperation(name, n, existQuans);
				bOperations.add(op);
				return;
			}
			}
		}
		throw new FrontEndException(String.format(
				"Expected an action at '%s' :\n%s", n.getOperator().getName()
						.toString(), n.getLocation().toString()));

	}

	/**
	 * 
	 * @throws ConfigFileErrorException
	 */

	private void findDefinitions() throws ConfigFileErrorException {
		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			visitExprNode(assumes[i].getAssume(), null);
		}

		if (inits != null) {
			for (int i = 0; i < inits.size(); i++) {
				visitExprNode(inits.get(i), null);
			}
		}
		if (bOperations != null) {
			for (int i = 0; i < bOperations.size(); i++) {
				visitExprNode(bOperations.get(i).getNode(), null);
			}
		}

		if (invariants != null) {
			for (int i = 0; i < invariants.size(); i++) {
				OpDefNode def = invariants.get(i);
				bDefinitionsSet.add(def);
				visitExprNode(def.getBody(), null);
			}
		}

		for (int i = 0; i < globalLets.size(); i++) {
			LetInNode letInNode = globalLets.get(i);
			for (int j = 0; j < letInNode.getLets().length; j++) {
				visitExprNode(letInNode.getLets()[j].getBody(), null);
			}
		}

	}

	/**
	 * @param exprOrOpArgNode
	 */
	private void visitExprOrOpArgNode(ExprOrOpArgNode n,
			FormalParamNode[] parameters) {
		if (n instanceof ExprNode) {
			visitExprNode((ExprNode) n, parameters);
		} else if (n instanceof OpArgNode) {

		}
	}

	private void visitExprNode(ExprNode node, FormalParamNode[] parameters) {
		switch (node.getKind()) {
		case OpApplKind: {
			visitOpApplNode((OpApplNode) node, parameters);
			return;
		}
		case LetInKind: {
			LetInNode l = (LetInNode) node;
			for (int i = 0; i < l.getLets().length; i++) {
				OpDefNode letDef = l.getLets()[i];

				if (parameters != null)
					letParams.put(letDef, parameters);

				visitExprNode(letDef.getBody(), letDef.getParams());
			}
			visitExprNode(l.getBody(), parameters);
			return;
		}

		}
	}

	/**
	 * @param node
	 * @throws ConfigFileErrorException
	 */
	private void visitOpApplNode(OpApplNode node, FormalParamNode[] parameters) {
		switch (node.getOperator().getKind()) {
		case ConstantDeclKind: {
			for (int i = 0; i < node.getArgs().length; i++) {
				visitExprOrOpArgNode(node.getArgs()[i], parameters);
			}
			return;
		}

		case VariableDeclKind: {
			for (int i = 0; i < node.getArgs().length; i++) {
				visitExprOrOpArgNode(node.getArgs()[i], parameters);
			}
			return;
		}

		case BuiltInKind: {
			visitBuiltInKind(node, parameters);
			return;
		}

		case UserDefinedOpKind: {
			OpDefNode def = (OpDefNode) node.getOperator();
			//TODO
			ModuleNode moduleNode = def.getSource().getOriginallyDefinedInModuleNode();
			if(moduleNode.getName().toString().equals("TLA2B")){
				return;
			}
			if (BBuiltInOPs.contains(def.getName())
					&& STANDARD_MODULES.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				
				for (int i = 0; i < node.getArgs().length; i++) {
					visitExprOrOpArgNode(node.getArgs()[i], parameters);
				}
				return;
			}
			bDefinitionsSet.add(def);
			visitExprNode(def.getBody(), def.getParams());

			for (int i = 0; i < node.getArgs().length; i++) {
				visitExprOrOpArgNode(node.getArgs()[i], parameters);
			}
			return;
		}

		}

	}

	/**
	 * @param node
	 */
	private void visitBuiltInKind(OpApplNode node, FormalParamNode[] parameters) {
		switch (BuiltInOPs.getOpCode(node.getOperator().getName())) {

		case OPCODE_be:
		case OPCODE_bf:
		case OPCODE_soa:
		case OPCODE_sso:
		case OPCODE_nrfs:
		case OPCODE_fc: {
			ExprNode[] in = node.getBdedQuantBounds();
			for (int i = 0; i < in.length; i++) {
				visitExprNode(in[i], parameters);
			}
			break;
		}
		case OPCODE_ite: {
			ifThenElseNodes.add(node);
			// if(!definitionMacro.contains(IF_THEN_ELSE)){
			// definitionMacro.add(IF_THEN_ELSE);
			// }
			break;
		}

		case OPCODE_bc: {
			if (!definitionMacros.contains(CHOOSE)) {
				definitionMacros.add(CHOOSE);
			}
			break;
		}
		case OPCODE_unchanged: {
			return;
		}
		}
		for (int i = 0; i < node.getArgs().length; i++) {
			visitExprOrOpArgNode(node.getArgs()[i], parameters);
		}
	}

	/**
	 * @throws NotImplementedException
	 * 
	 */
	private void evalRecursiveFunctions() throws NotImplementedException {

		for (OpDefNode def : bDefinitionsSet) {
			if (def.getBody() instanceof OpApplNode) {
				OpApplNode o = (OpApplNode) def.getBody();
				switch (getOpCode(o.getOperator().getName())) {
				case OPCODE_rfs: { // recursive Function
					bDefinitionsSet.remove(def);
					ifThenElseNodes.remove(o.getArgs()[0]);
					RecursiveFunktion rf = new RecursiveFunktion(def, o);
					recursiveFunctions.add(rf);
					return;
				}
				}
			}
		}
	}

	public void evalIfThenElse() {
		boolean b = false;
		for (int i = 0; i < ifThenElseNodes.size() && !b; i++) {
			OpApplNode node = ifThenElseNodes.get(i);
			TLAType t = (TLAType) node.getToolObject(TYPE_ID);
			if (t.getKind() != BOOL)
				b = true;
		}
		if (b)
			definitionMacros.add(IF_THEN_ELSE);
	}

	public ArrayList<LetInNode> getGlobalLets() {
		return this.globalLets;
	}

	public ArrayList<BOperation> getBOperations() {
		return this.bOperations;
	}

	public ArrayList<ExprNode> getInits() {
		return this.inits;
	}

	public ExprNode getNext() {
		return this.nextExpr;
	}

	public Set<OpDefNode> getBDefinitions() {
		return bDefinitionsSet;
	}

	public Hashtable<OpDefNode, FormalParamNode[]> getLetParams() {
		return letParams;
	}

	public ArrayList<String> getDefinitionMacros() {
		return definitionMacros;
	}

	public Set<OpDefNode> getUsedDefinitions() {
		return usedDefinitions;
	}

	public ArrayList<RecursiveFunktion> getRecursiveFunctions() {
		return recursiveFunctions;
	}
}
