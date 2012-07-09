/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Set;

import config.ConfigfileEvaluator;
import config.TLCValueNode;
import config.ValueObj;

import exceptions.FrontEndException;
import exceptions.TLA2BException;
import exceptions.NotImplementedException;
import exceptions.TypeErrorException;
import exceptions.UnificationException;
import global.BBuildIns;
import global.BBuiltInOPs;
import global.TranslationGlobals;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import types.*;
import util.StandardModules;

public class TypeChecker extends BuiltInOPs implements IType, ASTConstants,
		BBuildIns, TranslationGlobals {

	private final int TEMP_TYPE_ID = 6;
	private int paramId;

	private ArrayList<ExprNode> inits;
	private ExprNode nextExpr;
	private Set<OpDefNode> usedDefinitions;

	private ArrayList<OpApplNode> recList = new ArrayList<OpApplNode>();
	// every record node [a |-> 1 .. ] will be added to this List
	private ModuleNode moduleNode;
	private ArrayList<OpDeclNode> bConstList;

	private Hashtable<OpDeclNode, ValueObj> constantAssignments;

	/**
	 * @param moduleNode2
	 * @param conEval
	 * @param specAnalyser
	 */
	public TypeChecker(ModuleNode moduleNode, ConfigfileEvaluator conEval,
			SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		if (conEval != null) {
			this.bConstList = conEval.getbConstantList();
			this.constantAssignments = conEval.getConstantAssignments();
		}
		this.inits = specAnalyser.getInits();
		this.nextExpr = specAnalyser.getNext();
		usedDefinitions = specAnalyser.getUsedDefinitions();

		paramId = TYPE_ID;
	}

	public TypeChecker(ModuleNode moduleNode) {
		this.moduleNode = moduleNode;

		Set<OpDefNode> usedDefinitions = new HashSet<OpDefNode>();
		OpDefNode[] defs = moduleNode.getOpDefs();
		// used the last definition of the module
		usedDefinitions.add(defs[defs.length - 1]);
		this.usedDefinitions = usedDefinitions;

		paramId = TYPE_ID;
	}

	public void start() throws TLA2BException {
		OpDeclNode[] cons = moduleNode.getConstantDecls();
		for (int i = 0; i < cons.length; i++) {
			OpDeclNode con = cons[i];
			if (constantAssignments != null
					&& constantAssignments.containsKey(con)) {
				BType t = constantAssignments.get(con).getType();
				con.setToolObject(TYPE_ID, t);
			} else {
				Untyped u = new Untyped();
				con.setToolObject(TYPE_ID, u);
				u.addFollower(con);
			}
		}

		OpDeclNode[] vars = moduleNode.getVariableDecls();
		for (int i = 0; i < vars.length; i++) {
			OpDeclNode var = vars[i];
			Untyped u = new Untyped();
			var.setToolObject(TYPE_ID, u);
			u.addFollower(var);
		}

		evalDefinitions(moduleNode.getOpDefs());
		evalAssumptions(moduleNode.getAssumptions());

		if (inits != null) {
			for (int i = 0; i < inits.size(); i++) {
				visitExprNode(inits.get(i), BoolType.getInstance());
			}
		}

		if (nextExpr != null) {
			visitExprNode(nextExpr, BoolType.getInstance());
		}

		// check if a variable has no type
		for (int i = 0; i < vars.length; i++) {
			OpDeclNode var = vars[i];
			BType varType = (BType) var.getToolObject(TYPE_ID);
			if (varType.isUntyped()) {
				throw new TypeErrorException("Variable " + var.getName()
						+ " has no Type");
			}
		}

		// check if a constant has no type, only constants which will appear in
		// the resulting B Machine are considered
		for (int i = 0; i < cons.length; i++) {
			OpDeclNode con = cons[i];
			if (bConstList == null || bConstList.contains(con)) {
				BType conType = (BType) con.getToolObject(TYPE_ID);
				if (conType.isUntyped()) {
					throw new TypeErrorException("The type of Constant "
							+ con.getName() + " is still untyped: " + conType);
				}
			}
		}

		evalRecList();
	}

	/**
	 * 
	 */
	private void evalRecList() {
		for (int i = 0; i < recList.size(); i++) {
			OpApplNode n = recList.get(i);
			StructType struct = (StructType) n.getToolObject(TYPE_ID);
			ArrayList<String> fieldNames = new ArrayList<String>();
			ExprOrOpArgNode[] args = n.getArgs();
			for (int j = 0; j < args.length; j++) {
				OpApplNode pair = (OpApplNode) args[j];
				StringNode stringNode = (StringNode) pair.getArgs()[0];
				fieldNames.add(stringNode.getRep().toString());
			}
			for (int j = 0; j < struct.getFields().size(); j++) {
				String fieldName = struct.getFields().get(j);
				if (!fieldNames.contains(fieldName)
						&& struct.getType(fieldName).getKind() == MODELVALUE) {
					EnumType e = (EnumType) struct.getType(fieldName);
					e.setNoVal();
				}
			}
		}

	}

	private void evalDefinitions(OpDefNode[] opDefs) throws TLA2BException {
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
			// Definition in this module
			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
					.getName().toString())
					|| StandardModules.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}
			if (usedDefinitions.contains(def))
				visitOpDefNode(def);

		}

	}

	/**
	 * @param def
	 * @throws TLA2BException
	 */
	private void visitOpDefNode(OpDefNode def) throws TLA2BException {
		FormalParamNode[] params = def.getParams();
		for (int i = 0; i < params.length; i++) {
			FormalParamNode p = params[i];
			if (p.getArity() > 0) {
				throw new FrontEndException(String.format(
						"TLA2B do not support 2nd-order operators: '%s'\n %s ",
						def.getName(), def.getLocation()));
			}
			Untyped u = new Untyped();
			p.setToolObject(paramId, u);
			u.addFollower(p);
		}
		BType defType = visitExprNode(def.getBody(), new Untyped());
		def.setToolObject(TYPE_ID, defType);
		if (defType instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) defType).addFollower(def);
		}

	}

	private void evalAssumptions(AssumeNode[] assumptions)
			throws TLA2BException {
		for (AssumeNode assumeNode : assumptions) {
			visitExprNode(assumeNode.getAssume(), BoolType.getInstance());
		}
	}

	/**
	 * @param exprOrOpArgNode
	 * @param instance
	 * @throws TypeErrorException
	 * @throws NotImplementedException
	 */
	private BType visitExprOrOpArgNode(ExprOrOpArgNode n, BType expected)
			throws TLA2BException {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, expected);
		} else {
			throw new NotImplementedException("OpArgNode not implemented jet");
		}

	}

	private BType visitExprNode(ExprNode exprNode, BType expected)
			throws TLA2BException {

		switch (exprNode.getKind()) {
		case TLCValueKind: {
			TLCValueNode valueNode = (TLCValueNode) exprNode;
			try {
				return valueNode.getType().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found %s at '%s'(assigned in the configuration file),\n%s ",
								expected, valueNode.getType(),
								valueNode.getValue(), exprNode.getLocation()));
			}

		}

		case OpApplKind:
			return visitOpApplNode((OpApplNode) exprNode, expected);

		case NumeralKind:
			try {
				return IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at '%s',\n%s ", expected,
						((NumeralNode) exprNode).val(), exprNode.getLocation()));
			}
		case StringKind: {
			try {
				return StringType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found STRING at '%s',\n%s ", expected,
						((StringNode) exprNode).getRep(),
						exprNode.getLocation()));
			}
		}
		case AtNodeKind: { // @
			AtNode a = (AtNode) exprNode;
			OpApplNode pair2 = a.getExceptComponentRef();
			ExprOrOpArgNode rightside = pair2.getArgs()[1];
			BType type = (BType) rightside.getToolObject(TYPE_ID);
			try {
				BType res = type.unify(expected);
				return res;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at '@',\n%s ", expected,
						type,exprNode.getLocation()));
			}

		}

		case LetInKind: {
			LetInNode l = (LetInNode) exprNode;
			for (int i = 0; i < l.getLets().length; i++) {
				visitOpDefNode(l.getLets()[i]);
			}
			return visitExprNode(l.getBody(), expected);
		}

		case SubstInKind: {
			throw new RuntimeException(
					"SubstInKind should never occur after InstanceTransformation");
		}

		}

		throw new NotImplementedException(exprNode.toString(2));

	}

	/**
	 * @param n
	 * @param expected
	 * @return {@link BType}
	 * @throws TLA2BException
	 */
	private BType visitOpApplNode(OpApplNode n, BType expected)
			throws TLA2BException {

		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			OpDeclNode con = (OpDeclNode) n.getOperator();

			BType c = (BType) con.getToolObject(TYPE_ID);
			if (c == null) {
				throw new RuntimeException(con.getName() + " has no type yet!");
			}
			try {
				BType result = expected.unify(c);
				con.setToolObject(TYPE_ID, result);
				return result;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at constant '%s',\n%s",
						expected, c, con.getName(), n.getLocation())

				);
			}
		}

		case VariableDeclKind: {
			SymbolNode symbolNode = n.getOperator();
			String vName = symbolNode.getName().toString();
			BType v = (BType) symbolNode.getToolObject(TYPE_ID);
			if (v == null) {
				throw new RuntimeException(vName + " has no type yet!");
			}
			try {
				BType result = expected.unify(v);
				symbolNode.setToolObject(TYPE_ID, result);
				return result;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at variable '%s',\n%s",
						expected, v, vName, n.getLocation()));
			}
		}

		case BuiltInKind: {
			return evalBuiltInKind(n, expected);
		}

		case FormalParamKind: {
			SymbolNode symbolNode = n.getOperator();
			String pName = symbolNode.getName().toString();
			BType t = (BType) symbolNode.getToolObject(paramId);
			if (t == null) {
				t = (BType) symbolNode.getToolObject(TYPE_ID);
			}
			try {
				BType result = expected.unify(t);
				symbolNode.setToolObject(paramId, result);
				return result;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at parameter '%s',\n%s",
						expected, t, pName, n.getLocation()));
			}
		}

		case UserDefinedOpKind: {
			OpDefNode def = (OpDefNode) n.getOperator();

			// Definition is a BBuilt-in definition
			if (BBuiltInOPs.contains(def.getName())) {
				return evalBBuiltIns(n, expected);
			}

			BType found = ((BType) def.getToolObject(TYPE_ID));
			if (found == null)
				found = new Untyped();
			// throw new RuntimeException(def.getName() + " has no type yet!");
			found = found.cloneBType();
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at definition '%s',\n%s",
						expected, found, def.getName(), n.getLocation()));
			}
			boolean untyped = false;
			FormalParamNode[] params = def.getParams();
			for (int i = 0; i < n.getArgs().length; i++) {
				// clone the parameter type, because the parameter type is not
				// set/changed at a definition call
				FormalParamNode p = params[i];
				BType pType = ((BType) p.getToolObject(TYPE_ID));
				if (pType == null) {
					pType = new Untyped();
//					throw new RuntimeException("Parameter " + p.getName()
//							+ " has no type yet!\n" + p.getLocation());
				}
				pType = pType.cloneBType();
				if (pType.isUntyped())
					untyped = true;

				pType = visitExprOrOpArgNode(n.getArgs()[i], pType); // unify
																		// both
																		// types
				// set types of the arguments of the definition call to the
				// parameters for reevaluation the def body
				p.setToolObject(TEMP_TYPE_ID, pType);
			}

			if (found.isUntyped() || untyped) {
				// evaluate the body of the definition again
				paramId = TEMP_TYPE_ID;
				found = visitExprNode(def.getBody(), found);
				paramId = TYPE_ID;
			}

			n.setToolObject(TYPE_ID, found);

			return found;

		}

		default: {
			throw new NotImplementedException(n.getOperator().getName()
					.toString());
		}
		}

	}

	/**
	 * @param exprNode
	 * @param expected
	 * @return {@link BType}
	 * @throws TLA2BException
	 */
	private BType evalBuiltInKind(OpApplNode n, BType expected)
			throws TLA2BException {

		switch (getOpCode(n.getOperator().getName())) {

		/**********************************************************************
		 * equality and disequality: =, #, /=
		 **********************************************************************/
		case OPCODE_eq: // =
		case OPCODE_noteq: // /=, #
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			BType left = visitExprOrOpArgNode(n.getArgs()[0],
					new types.Untyped());
			visitExprOrOpArgNode(n.getArgs()[1], left);
			return BoolType.getInstance();
		}

		/**********************************************************************
		 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
		 **********************************************************************/
		case OPCODE_neg: // Negation
		case OPCODE_lnot: // Negation
		case OPCODE_cl: // $ConjList
		case OPCODE_dl: // $DisjList
		case OPCODE_land: // \land
		case OPCODE_lor: // \lor
		case OPCODE_equiv: // \equiv
		case OPCODE_implies: // =>
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			for (int i = 0; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], BoolType.getInstance());
			}
			return BoolType.getInstance();
		}

		/**********************************************************************
		 * Quantification: \A x \in S : P or \E x \in S : P
		 **********************************************************************/
		case OPCODE_be: // \E x \in S : P
		case OPCODE_bf: // \A x \in S : P
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			evalBoundedVariables(n);
			visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
			return BoolType.getInstance();
		}

		/**********************************************************************
		 * Set Operators
		 **********************************************************************/
		case OPCODE_se: // SetEnumeration {..}
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at set enumeration,\n%s",
						expected, n.getLocation()));
			}
			BType current = found.getSubType();
			for (int i = 0; i < n.getArgs().length; i++) {
				current = visitExprOrOpArgNode(n.getArgs()[i], current);
			}
			return found;
		}

		case OPCODE_in: // \in
		case OPCODE_notin: // \notin
		{
			if (!BoolType.getInstance().compare(expected)) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			BType element = visitExprOrOpArgNode(n.getArgs()[0], new Untyped());
			visitExprOrOpArgNode(n.getArgs()[1], new PowerSetType(element));

			return BoolType.getInstance();
		}

		case OPCODE_setdiff: // set difference
		case OPCODE_cup: // set union
		case OPCODE_cap: // set intersection
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			BType left = visitExprOrOpArgNode(n.getArgs()[0], found);
			BType right = visitExprOrOpArgNode(n.getArgs()[1], left);
			return right;
		}

		case OPCODE_subseteq: // \subseteq - subset or equal
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			BType left = visitExprOrOpArgNode(n.getArgs()[0], new PowerSetType(
					new Untyped()));
			visitExprOrOpArgNode(n.getArgs()[1], left);
			return BoolType.getInstance();
		}

		/**********************************************************************
		 * Set Constructor
		 **********************************************************************/
		case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}

			if (n.isBdedQuantATuple()[0]) {
				throw new TypeErrorException(
						"A tuple as parameter within the set constructor is not permitted.\n"
								+ n.getLocation());
			}
			ExprNode[] bounds = n.getBdedQuantBounds();
			PowerSetType S = (PowerSetType) visitExprNode(bounds[0], found);
			BType xType = S.getSubType();

			FormalParamNode x = n.getBdedQuantSymbolLists()[0][0];
			x.setToolObject(TYPE_ID, xType);
			if (xType instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) xType).addFollower(x);
			}

			visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
			return S;
		}

		case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			evalBoundedVariables(n);
			visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
			return found;
		}

		case OPCODE_subset: // SUBSET (conforms POW in B)
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at 'SUBSET',\n%s",
						expected, n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
			return found;
		}

		case OPCODE_union: // Union - Union{{1},{2}}
		{
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at 'SUBSET',\n%s",
						expected, n.getLocation()));
			}
			PowerSetType setOfSet = (PowerSetType) visitExprOrOpArgNode(
					n.getArgs()[0], new PowerSetType(found));
			return setOfSet.getSubType();
		}

		/**********************************************************************
		 * Prime
		 **********************************************************************/
		case OPCODE_prime: // prime
		{
			try {
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				if (node.getOperator().getKind() != VariableDeclKind) {
					throw new TypeErrorException("Expected variable at \""
							+ node.getOperator().getName() + "\":\n"
							+ node.getLocation());
				}
				return visitExprOrOpArgNode(n.getArgs()[0], expected);
			} catch (ClassCastException e) {
				throw new TypeErrorException(
						"Expected variable as argument of prime operator:\n"
								+ n.getArgs()[0].getLocation());
			}
		}

		/***********************************************************************
		 * Tuple: Tuple as Function 1..n to Set (Sequence)
		 ***********************************************************************/
		case OPCODE_tup: // $Tuple
		{
			PowerSetType found = new PowerSetType(new PairType(
					IntType.getInstance(), new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found POW(INTEGER*UNTYPED) at Tuple,\n%s",
								expected, n.getLocation()));
			}
			PairType pair = (PairType) found.getSubType();
			BType current = pair.getSecond();
			for (int i = 0; i < n.getArgs().length; i++) {
				current = visitExprOrOpArgNode(n.getArgs()[i], current);
			}
			pair.setSecond(current);
			return found;
		}

		/***********************************************************************
		 * Function constructors
		 ***********************************************************************/
		case OPCODE_rfs: // recursive function ( f[x\in Nat] == IF x = 0 THEN 1
							// ELSE f[n-1]
		{
			ArrayList<BType> domList = new ArrayList<BType>();
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ExprNode[] bounds = n.getBdedQuantBounds();
			for (int i = 0; i < bounds.length; i++) {
				if (n.isBdedQuantATuple()[i]) {
					throw new TypeErrorException(
							"A tuple of bounded variable is not permitted.\n"
									+ n.getLocation());
				}
				PowerSetType S = (PowerSetType) visitExprNode(bounds[i],
						new PowerSetType(new Untyped()));
				BType pType = S.getSubType();
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode p = params[i][j];
					p.setToolObject(TYPE_ID, pType);
					if (pType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) pType).addFollower(p);
					}
					domList.add(pType);
				}
			}
			BType domType = makePair(domList);

			PowerSetType found = new PowerSetType(new PairType(domType,
					new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at FunctionConstructor,\n%s",
						expected, found, n.getLocation()));
			}
			FormalParamNode recFunc = n.getUnbdedQuantSymbols()[0];
			recFunc.setToolObject(TYPE_ID, found);
			found.addFollower(recFunc);

			PairType pair = (PairType) found.getSubType();
			visitExprOrOpArgNode(n.getArgs()[0], pair.getSecond());

			return found;
		}

		case OPCODE_nrfs: // succ[n \in Nat] == n + 1
		case OPCODE_fc: // [n \in Nat |-> n+1]
		{
			ArrayList<BType> domList = new ArrayList<BType>();
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ExprNode[] bounds = n.getBdedQuantBounds();
			for (int i = 0; i < bounds.length; i++) {
				if (n.isBdedQuantATuple()[i]) {
					throw new TypeErrorException(
							"A tuple of bounded variable is not permitted.\n"
									+ n.getLocation());
				}
				PowerSetType S = (PowerSetType) visitExprNode(bounds[i],
						new PowerSetType(new Untyped()));
				BType pType = S.getSubType();
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode p = params[i][j];
					p.setToolObject(TYPE_ID, pType);
					if (pType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) pType).addFollower(p);
					}
					domList.add(pType);
				}
			}
			BType domType = makePair(domList);

			PowerSetType found = new PowerSetType(new PairType(domType,
					new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at FunctionConstructor,\n%s",
						expected, found, n.getLocation()));
			}
			PairType pair = (PairType) found.getSubType();
			visitExprOrOpArgNode(n.getArgs()[0], pair.getSecond());

			return found;
		}

		/***********************************************************************
		 * Function call
		 ***********************************************************************/
		case OPCODE_fa: // $FcnApply f[1]
		{
			BType domType;
			ExprOrOpArgNode dom = n.getArgs()[1];
			if (dom instanceof OpApplNode
					&& ((OpApplNode) dom).getOperator().getName().toString()
							.equals("$Tuple")) {
				ArrayList<BType> domList = new ArrayList<BType>();
				OpApplNode domOpAppl = (OpApplNode) dom;
				for (int i = 0; i < domOpAppl.getArgs().length; i++) {
					BType d = visitExprOrOpArgNode(domOpAppl.getArgs()[i],
							new Untyped());
					domList.add(d);
				}
				domType = makePair(domList);
			} else {
				domType = visitExprOrOpArgNode(n.getArgs()[1], new Untyped());
			}
			PowerSetType func = new PowerSetType(
					new PairType(domType, expected));
			PowerSetType res = (PowerSetType) visitExprOrOpArgNode(
					n.getArgs()[0], func);
			PairType pair = (PairType) res.getSubType();
			return pair.getSecond();
		}

		/***********************************************************************
		 * Domain of Function
		 ***********************************************************************/
		case OPCODE_domain: {
			PowerSetType found = new PowerSetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at 'DOMAIN',\n%s",
						expected, n.getLocation()));
			}
			PowerSetType func = new PowerSetType(new PairType(
					found.getSubType(), new Untyped()));

			visitExprOrOpArgNode(n.getArgs()[0], func);
			return found;
		}
		/***********************************************************************
		 * Set of Function
		 ***********************************************************************/
		case OPCODE_sof: // [ A -> B]
		{
			PowerSetType found = new PowerSetType(new PowerSetType(
					new PairType()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found POW(POW(_A*_B)) at Set of Function,\n%s",
								expected, n.getLocation()));
			}
			PairType pair = (PairType) ((PowerSetType) found.getSubType())
					.getSubType();
			visitExprOrOpArgNode(n.getArgs()[0],
					new PowerSetType(pair.getFirst()));
			visitExprOrOpArgNode(n.getArgs()[1],
					new PowerSetType(pair.getSecond()));
			return found;
		}

		/**********************************************************************
		 * Except
		 **********************************************************************/
		case OPCODE_exc: // Except
		{
			return evalExcept(n, expected);
		}

		/***********************************************************************
		 * Cartesian Product: A \X B
		 ***********************************************************************/
		case OPCODE_cp: // $CartesianProd A \X B \X C as $CartesianProd(A, B, C)
		{
			ArrayList<BType> list = new ArrayList<BType>();
			for (int i = 0; i < n.getArgs().length; i++) {
				PowerSetType t = (PowerSetType) visitExprOrOpArgNode(
						n.getArgs()[i], new PowerSetType(new Untyped()));
				list.add(t.getSubType());
			}

			PowerSetType found = new PowerSetType(makePair(list));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at Cartesian Product,\n%s",
						expected, found, n.getLocation()));
			}
			return found;
		}

		/***********************************************************************
		 * Records
		 ***********************************************************************/
		case OPCODE_sor: // $SetOfRcds [L1 : e1, L2 : e2]
		{
			StructType struct = new StructType();
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				StringNode field = (StringNode) pair.getArgs()[0];
				PowerSetType fieldType = (PowerSetType) visitExprOrOpArgNode(
						pair.getArgs()[1], new PowerSetType(new Untyped()));
				struct.add(field.getRep().toString(), fieldType.getSubType());
			}

			PowerSetType found = new PowerSetType(struct);
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at Set of Records,\n%s",
						expected, found, n.getLocation()));
			}
			n.setToolObject(TYPE_ID, found);
			if (found instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) found).addFollower(n);
			}
			return found;
		}

		case OPCODE_rc: // [h_1 |-> 1, h_2 |-> 2]
		{
			StructType found = new StructType();
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				StringNode field = (StringNode) pair.getArgs()[0];
				BType fieldType = visitExprOrOpArgNode(pair.getArgs()[1],
						new Untyped());
				found.add(field.getRep().toString(), fieldType);
			}
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at Record,\n%s", expected,
						found, n.getLocation()));
			}
			n.setToolObject(TYPE_ID, found);
			if (found instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) found).addFollower(n);
			}
			recList.add(n);
			return found;

		}

		case OPCODE_rs: // $RcdSelect r.c
		{
			String fieldName = ((StringNode) n.getArgs()[1]).getRep()
					.toString();
			StructType r = (StructType) visitExprOrOpArgNode(n.getArgs()[0],
					new StructType());

			StructType expectedStruct = new StructType();
			expectedStruct.add(fieldName, expected);

			try {
				r = r.unify(expectedStruct);
				return r.getType(fieldName);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Struct has no field %s with type %s: %s\n%s",
						fieldName, r.getType(fieldName), r, n.getLocation()));
			}
		}

		/***********************************************************************
		 * miscellaneous constructs
		 ***********************************************************************/
		case OPCODE_ite: // IF THEN ELSE
		{
			visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
			BType then = visitExprOrOpArgNode(n.getArgs()[1], expected);
			BType eelse = visitExprOrOpArgNode(n.getArgs()[2], then);
			n.setToolObject(TYPE_ID, eelse);
			if (eelse instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) eelse).addFollower(n);
			}
			return eelse;
		}

		case OPCODE_case: {
			/**
			 * CASE p1 -> e1 [] p2 -> e2 represented as $Case( $Pair(p1,
			 * e1),$Pair(p2, e2) ) and CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
			 * represented as $Case( $Pair(p1, e1), $Pair(p2, e2), $Pair(null,
			 * e3))
			 **/
			BType found = expected;
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				if (pair.getArgs()[0] != null) {
					visitExprOrOpArgNode(pair.getArgs()[0],
							BoolType.getInstance());
				}
				found = visitExprOrOpArgNode(pair.getArgs()[1], found);
			}
			return found;

		}

		case OPCODE_bc: { // CHOOSE x \in S: P
			if (n.isBdedQuantATuple()[0]) {
				throw new TypeErrorException(
						"A tuple as parameter within the set constructor is not permitted.\n"
								+ n.getLocation());
			}
			ExprNode[] bounds = n.getBdedQuantBounds();
			PowerSetType S = (PowerSetType) visitExprNode(bounds[0],
					new PowerSetType(new Untyped()));
			BType found = S.getSubType();

			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'CHOOSE',\n%s", expected,
						found, n.getLocation()));
			}
			FormalParamNode x = n.getBdedQuantSymbolLists()[0][0];
			x.setToolObject(TYPE_ID, found);
			if (found instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) found).addFollower(x);
			}
			visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
			return found;
		}

		case OPCODE_unchanged: {
			return BoolType.getInstance().unify(expected);
		}

		/***********************************************************************
		 * no TLA+ Built-ins
		 ***********************************************************************/
		case 0: {
			return evalBBuiltIns(n, expected);
		}
		}

		throw new NotImplementedException("Not supported Operator: "
				+ n.getOperator().getName().toString() + "\n" + n.getLocation());
	}

	/**
	 * @param n
	 * @param expected
	 * @return
	 * @throws TLA2BException
	 */
	private BType evalExcept(OpApplNode n, BType expected)
			throws TLA2BException {
		BType t = visitExprOrOpArgNode(n.getArgs()[0], expected);
		n.setToolObject(TYPE_ID, t);
		if (t instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) t).addFollower(n);
		}

		for (int i = 1; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];
			ExprOrOpArgNode leftside = pair.getArgs()[0];
			ExprOrOpArgNode rightside = pair.getArgs()[1];
			// stored for @ node
			Untyped untyped = new Untyped();
			rightside.setToolObject(TYPE_ID, untyped);
			untyped.addFollower(rightside);
			BType valueType = visitExprOrOpArgNode(rightside, untyped);
			
			OpApplNode seq = (OpApplNode) leftside;
			LinkedList<ExprOrOpArgNode> list = new LinkedList<ExprOrOpArgNode>();
			for (int j = 0; j < seq.getArgs().length; j++) {
				list.add(seq.getArgs()[j]);
			}
			ExprOrOpArgNode first = list.poll();

			if (first instanceof StringNode) {
				String field = ((StringNode) first).getRep().toString();
				
				BType res = evalType(list, valueType);
				StructOrFunction s = new StructOrFunction(field, res);
				try {
					t = t.unify(s);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format(
							"Expected %s, found %s at 'EXCEPT',\n%s", t, s,
							pair.getLocation()));
				}

			} else {
				ExprOrOpArgNode domExpr = first;
				BType domType;
				BType rangeType;
				if (domExpr instanceof OpApplNode
						&& ((OpApplNode) domExpr).getOperator().getName()
								.toString().equals("$Tuple")) {
					ArrayList<BType> domList = new ArrayList<BType>();
					OpApplNode domOpAppl = (OpApplNode) domExpr;
					for (int j = 0; j < domOpAppl.getArgs().length; j++) {
						BType d = visitExprOrOpArgNode(domOpAppl.getArgs()[j],
								new Untyped());
						domList.add(d);
					}
					domType = makePair(domList);
				} else {
					domType = visitExprOrOpArgNode(domExpr, new Untyped());
				}
				rangeType = evalType(list, valueType);
				PowerSetType p = new PowerSetType(new PairType(domType,
						rangeType));
				try {
					t = t.unify(p);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format(
							"Expected %s, found %s at 'EXCEPT',\n%s", t, p,
							pair.getLocation()));
				}
			}
		}
		return t;

	}

	/**
	 * @param list
	 * @param valueType
	 * @return
	 * @throws TLA2BException
	 */
	private BType evalType(LinkedList<ExprOrOpArgNode> list, BType valueType)
			throws TLA2BException {
		if (list.size() == 0) {
			return valueType;
		}
		ExprOrOpArgNode head = list.poll();
		if (head instanceof StringNode) {
			// record or function of strings
			String name = ((StringNode) head).getRep().toString();
			StructOrFunction res = new StructOrFunction(name, evalType(list,
					valueType));
			return res;
		}
		BType t = visitExprOrOpArgNode(head, new Untyped());
		PowerSetType res = new PowerSetType(new PairType(t, evalType(list,
				valueType)));
		return res;
	}

	private BType evalBBuiltIns(OpApplNode n, BType expected)
			throws TLA2BException {
		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {
		// B Builtins

		/**********************************************************************
		 * Standard Module Naturals
		 **********************************************************************/
		case B_OPCODE_gt: // >
		case B_OPCODE_lt: // <
		case B_OPCODE_leq: // <=
		case B_OPCODE_geq: // >=
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			for (int i = 0; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], IntType.getInstance());
			}
			return BoolType.getInstance();
		}

		case B_OPCODE_plus: // +
		case B_OPCODE_minus: // -
		case B_OPCODE_times: // *
		case B_OPCODE_div: // /
		case B_OPCODE_mod: // % modulo
		case B_OPCODE_exp: { // x hoch y, x^y
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			for (int i = 0; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], IntType.getInstance());
			}
			return IntType.getInstance();
		}

		case B_OPCODE_dotdot: // ..
		{
			try {
				expected.unify(new PowerSetType(IntType.getInstance()));
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER) at '..',\n%s",
						expected, n.getLocation()));
			}

			for (int i = 0; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], IntType.getInstance());
			}
			return new PowerSetType(IntType.getInstance());
		}

		case B_OPCODE_nat: // Nat
		{
			try {
				PowerSetType found = new PowerSetType(IntType.getInstance());
				found = found.unify(expected);
				return found;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER) at 'Nat',\n%s",
						expected, n.getLocation()));
			}
		}

		/**********************************************************************
		 * Standard Module Integers
		 **********************************************************************/
		case B_OPCODE_int: // Int
		{
			try {
				PowerSetType found = new PowerSetType(IntType.getInstance());
				found = found.unify(expected);
				return found;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER) at 'Int',\n%s",
						expected, n.getLocation()));
			}
		}

		case B_OPCODE_uminus: // -x
		{
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at '-',\n%s", expected,
						n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0], IntType.getInstance());
			return IntType.getInstance();
		}

		/**********************************************************************
		 * Standard Module FiniteSets
		 **********************************************************************/
		case B_OPCODE_finite: // IsFiniteSet
		{
			try {
				BoolType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at 'IsFiniteSet',\n%s",
						expected, n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0],
					new PowerSetType(new Untyped()));
			return BoolType.getInstance();
		}

		case B_OPCODE_card: // Cardinality
		{
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at 'Cardinality',\n%s",
						expected, n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0],
					new PowerSetType(new Untyped()));
			return IntType.getInstance();
		}

		/**********************************************************************
		 * Standard Module Sequences
		 **********************************************************************/
		case B_OPCODE_seq: { // Seq(S) - set of sequences, S must be a set

			PowerSetType set_of_seq = new PowerSetType(new PowerSetType(
					new PairType(IntType.getInstance(), new Untyped())));

			try {
				set_of_seq = set_of_seq.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found POW(POW(INTEGER*_A)) at 'Seq',\n%s",
								expected, n.getLocation()));
			}
			PowerSetType seq = (PowerSetType) set_of_seq.getSubType();
			PairType pair = (PairType) seq.getSubType();
			PowerSetType S = (PowerSetType) visitExprOrOpArgNode(
					n.getArgs()[0], new PowerSetType(pair.getSecond()));
			pair.setSecond(S.getSubType());
			return set_of_seq;
		}

		case B_OPCODE_len: // lengh of the sequence
		{
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at 'Len',\n%s", expected,
						n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0],
					new PowerSetType(new Untyped()));
			return IntType.getInstance();
		}

		case B_OPCODE_conc: // s \o s2 - concatenation of s and s2
		{
			PowerSetType found = new PowerSetType(new PairType(
					IntType.getInstance(), new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER*_A) at '\\o',\n%s",
						expected, n.getLocation()));
			}
			BType left = visitExprOrOpArgNode(n.getArgs()[0], found);
			BType right = visitExprOrOpArgNode(n.getArgs()[1], left);
			return right;
		}

		case B_OPCODE_append: // Append(s, e)
		{
			PowerSetType found = new PowerSetType(new PairType(
					IntType.getInstance(), new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER*_A) at 'Append',\n%s",
						expected, n.getLocation()));
			}
			BType s = visitExprOrOpArgNode(n.getArgs()[0], found);
			PairType pair = (PairType) ((PowerSetType) s).getSubType();
			BType e = visitExprOrOpArgNode(n.getArgs()[1], pair.getSecond());
			pair.setSecond(e);
			return s;
		}

		case B_OPCODE_head: // HEAD(s) - the first element of the sequence
		{
			PowerSetType seq = new PowerSetType(new PairType(
					IntType.getInstance(), expected));
			BType s = visitExprOrOpArgNode(n.getArgs()[0], seq);
			PairType res = (PairType) ((PowerSetType) s).getSubType();
			return res.getSecond();
		}

		case B_OPCODE_tail: // Tail(s)
		{
			PowerSetType found = new PowerSetType(new PairType(
					IntType.getInstance(), new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found POW(INTEGER*UNTYED) at 'Tail',\n%s",
								expected, n.getLocation()));
			}
			BType s = visitExprOrOpArgNode(n.getArgs()[0], found);
			return s;
		}

		case B_OPCODE_subseq: // SubSeq(s,m,n)
		{
			PowerSetType found = new PowerSetType(new PairType(
					IntType.getInstance(), new Untyped()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found POW(INTEGER*UNTYED) at 'SubSeq',\n%s",
								expected, n.getLocation()));
			}
			BType s = visitExprOrOpArgNode(n.getArgs()[0], found);
			visitExprOrOpArgNode(n.getArgs()[1], IntType.getInstance());
			visitExprOrOpArgNode(n.getArgs()[2], IntType.getInstance());
			return s;
		}

		// TODO add BSeq to tla standard modules

		/**********************************************************************
		 * Standard Module TLA2B
		 **********************************************************************/

		case B_OPCODE_min: // MinOfSet(S)
		case B_OPCODE_max: // MaxOfSet(S)
		case B_OPCODE_setprod: // SetProduct(S)
		case B_OPCODE_setsum: // SetSummation(S)
		{
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0],
					new PowerSetType(IntType.getInstance()));
			return IntType.getInstance();
		}

		case B_OPCODE_permseq: // PermutedSequences(S)
		{
			PowerSetType argType = (PowerSetType) visitExprOrOpArgNode(
					n.getArgs()[0], new PowerSetType(new Untyped()));

			PowerSetType found = new PowerSetType(new PowerSetType(
					new PairType(IntType.getInstance(), argType.getSubType())));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'PermutedSequences',\n%s",
						expected, found, n.getLocation()));
			}
			return found;
		}

		/***********************************************************************
		 * TLA+ Built-Ins, but not in tlc.tool.BuiltInOPs
		 ***********************************************************************/
		case B_OPCODE_bool: // BOOLEAN
			try {
				PowerSetType found = new PowerSetType(BoolType.getInstance());
				found = found.unify(expected);
				return found;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(BOOL) at 'BOOLEAN',\n%s",
						expected, n.getLocation()));
			}

		case B_OPCODE_string: // STRING
			try {
				PowerSetType found = new PowerSetType(StringType.getInstance());
				found = found.unify(expected);
				return found;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(STRING) at 'STRING',\n%s",
						expected, n.getLocation()));
			}

		case B_OPCODE_true:
		case B_OPCODE_false:
			try {
				BoolType.getInstance().unify(expected);
				return BoolType.getInstance();
			} catch (Exception e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found BOOL at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}

		default: {
			throw new NotImplementedException(n.getOperator().getName()
					.toString());
		}
		}
	}

	public static BType makePair(ArrayList<BType> list) {
		if (list.size() == 0)
			throw new RuntimeException("emptylist");
		if (list.size() == 1)
			return list.get(0);
		PairType p = new PairType();
		p.setFirst(list.get(0));
		for (int i = 1; i < list.size(); i++) {
			p.setSecond(list.get(i));
			if (i < list.size() - 1) {
				p = new PairType(p, null);
			}
		}
		return p;
	}

	/**
	 * @param n
	 * @throws TLA2BException
	 */
	private void evalBoundedVariables(OpApplNode n) throws TLA2BException {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] bounds = n.getBdedQuantBounds();
		for (int i = 0; i < bounds.length; i++) {
			if (n.isBdedQuantATuple()[i]) {
				throw new TypeErrorException(
						"A tuple of bounded variable is not permitted.\n"
								+ n.getLocation());
			}
			PowerSetType S = (PowerSetType) visitExprNode(bounds[i],
					new PowerSetType(new Untyped()));
			BType pType = S.getSubType();
			for (int j = 0; j < params[i].length; j++) {
				FormalParamNode p = params[i][j];
				p.setToolObject(TYPE_ID, pType);
				if (pType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) pType).addFollower(p);
				}
			}
		}
	}

}
