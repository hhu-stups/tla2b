/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Set;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.TLCValueNode;
import de.tla2b.config.ValueObj;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.*;

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
				TLAType t = constantAssignments.get(con).getType();
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
			TLAType varType = (TLAType) var.getToolObject(TYPE_ID);
			if (varType.isUntyped()) {
				throw new TypeErrorException("Variable '" + var.getName()
						+ "' has no cype!");
			}
		}

		// check if a constant has no type, only constants which will appear in
		// the resulting B Machine are considered
		for (int i = 0; i < cons.length; i++) {
			OpDeclNode con = cons[i];
			if (bConstList == null || bConstList.contains(con)) {
				TLAType conType = (TLAType) con.getToolObject(TYPE_ID);
				if (conType.isUntyped()) {
					throw new TypeErrorException("The type of constant "
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
			String moduleName1 = def.getOriginallyDefinedInModuleNode()
					.getName().toString();
			String moduleName2 = def.getSource()
					.getOriginallyDefinedInModuleNode().getName().toString();

			if (STANDARD_MODULES.contains(moduleName1)
					|| STANDARD_MODULES.contains(moduleName2)) {
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
		TLAType defType = visitExprNode(def.getBody(), new Untyped());
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
	private TLAType visitExprOrOpArgNode(ExprOrOpArgNode n, TLAType expected)
			throws TLA2BException {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, expected);
		} else {
			throw new NotImplementedException("OpArgNode not implemented jet");
		}

	}

	private TLAType visitExprNode(ExprNode exprNode, TLAType expected)
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
			TLAType type = (TLAType) rightside.getToolObject(TYPE_ID);
			try {
				TLAType res = type.unify(expected);
				return res;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at '@',\n%s ", expected, type,
						exprNode.getLocation()));
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

		case DecimalKind:{
			// currently not supported
		}
		
		
		}

		throw new NotImplementedException(exprNode.toString(2));

	}

	/**
	 * @param n
	 * @param expected
	 * @return {@link TLAType}
	 * @throws TLA2BException
	 */
	private TLAType visitOpApplNode(OpApplNode n, TLAType expected)
			throws TLA2BException {

		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			OpDeclNode con = (OpDeclNode) n.getOperator();

			TLAType c = (TLAType) con.getToolObject(TYPE_ID);
			if (c == null) {
				throw new RuntimeException(con.getName() + " has no type yet!");
			}
			try {
				TLAType result = expected.unify(c);
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
			TLAType v = (TLAType) symbolNode.getToolObject(TYPE_ID);
			if (v == null) {
				throw new RuntimeException(vName + " has no type yet!");
			}
			try {
				TLAType result = expected.unify(v);
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
			TLAType t = (TLAType) symbolNode.getToolObject(paramId);
			if (t == null) {
				t = (TLAType) symbolNode.getToolObject(TYPE_ID);
			}
			try {
				TLAType result = expected.unify(t);
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
			String sourceModule = def.getSource()
					.getOriginallyDefinedInModuleNode().getName().toString();
			if (BBuiltInOPs.contains(def.getName())
					&& STANDARD_MODULES.contains(sourceModule)) {
				return evalBBuiltIns(n, expected);
			}

			TLAType found = ((TLAType) def.getToolObject(TYPE_ID));
			if (found == null)
				found = new Untyped();
			// throw new RuntimeException(def.getName() + " has no type yet!");
			found = found.cloneTLAType();
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
				TLAType pType = ((TLAType) p.getToolObject(TYPE_ID));
				if (pType == null) {
					pType = new Untyped();
					// throw new RuntimeException("Parameter " + p.getName()
					// + " has no type yet!\n" + p.getLocation());
				}
				pType = pType.cloneTLAType();
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
	 * @return {@link TLAType}
	 * @throws TLA2BException
	 */
	private TLAType evalBuiltInKind(OpApplNode n, TLAType expected)
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
			TLAType left = visitExprOrOpArgNode(n.getArgs()[0],
					new de.tla2b.types.Untyped());
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
			SetType found = new SetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at set enumeration,\n%s",
						expected, n.getLocation()));
			}
			TLAType current = found.getSubType();
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
			TLAType element = visitExprOrOpArgNode(n.getArgs()[0],
					new Untyped());
			visitExprOrOpArgNode(n.getArgs()[1], new SetType(element));

			return BoolType.getInstance();
		}

		case OPCODE_setdiff: // set difference
		case OPCODE_cup: // set union
		case OPCODE_cap: // set intersection
		{
			SetType found = new SetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			TLAType left = visitExprOrOpArgNode(n.getArgs()[0], found);
			TLAType right = visitExprOrOpArgNode(n.getArgs()[1], left);
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
			TLAType left = visitExprOrOpArgNode(n.getArgs()[0], new SetType(
					new Untyped()));
			visitExprOrOpArgNode(n.getArgs()[1], left);
			return BoolType.getInstance();
		}

		/**********************************************************************
		 * Set Constructor
		 **********************************************************************/
		case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
		{

			TLAType domainType = evalBoundedVariables(n);
			SetType found = new SetType(domainType);
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at '%s',\n%s", expected, found,
						n.getOperator().getName(), n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
			return found;
		}

		case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
		{
			SetType found = new SetType(new Untyped());
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
			SetType found = new SetType(new Untyped());
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
			SetType found = new SetType(new Untyped());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A) at 'SUBSET',\n%s",
						expected, n.getLocation()));
			}
			SetType setOfSet = (SetType) visitExprOrOpArgNode(n.getArgs()[0],
					new SetType(found));
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
		case OPCODE_tup: { // $Tuple
			ArrayList<TLAType> list = new ArrayList<TLAType>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNode(n.getArgs()[i], new Untyped()));
			}
			TLAType found = null;
			if (list.size() == 0) {
				found = new FunctionType(IntType.getInstance(), new Untyped());
			} else if (list.size() == 1) {
				found = new FunctionType(IntType.getInstance(), list.get(0));
			} else {
				found = new TupleType(list);
			}
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at Tuple,\n%s", expected, found,
						n.getLocation()));
			}
			n.setToolObject(TYPE_ID, found);
			if (found instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) found).addFollower(n);
			}
			return found;
		}

		/***********************************************************************
		 * Function constructors
		 ***********************************************************************/
		case OPCODE_rfs: // recursive function ( f[x\in Nat] == IF x = 0 THEN 1
							// ELSE f[n-1]
		{

			FormalParamNode recFunc = n.getUnbdedQuantSymbols()[0];
			FunctionType recType = new FunctionType();
			recFunc.setToolObject(TYPE_ID, recType);
			recType.addFollower(recFunc);

			TLAType domainType = evalBoundedVariables(n);
			FunctionType found = new FunctionType(domainType, new Untyped());
			visitExprOrOpArgNode(n.getArgs()[0], found.getRange());

			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException("Expected '" + expected
						+ "', found '" + found + "'.\n" + n.getLocation());
			}

			TLAType t = null;
			try {
				t = (TLAType) recFunc.getToolObject(TYPE_ID);
				found = found.unify(t);
			} catch (UnificationException e) {
				throw new TypeErrorException("Expected '" + expected
						+ "', found '" + t + "'.\n" + n.getLocation());
			}

			return found;
		}

		case OPCODE_nrfs: // succ[n \in Nat] == n + 1
		case OPCODE_fc: // [n \in Nat |-> n+1]
		{
			TLAType domainType = evalBoundedVariables(n);
			FunctionType found = new FunctionType(domainType, new Untyped());
			visitExprOrOpArgNode(n.getArgs()[0], found.getRange());

			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException("Expected '" + expected
						+ "', found '" + found + "'.\n" + n.getLocation());
			}
			return found;
		}

		/***********************************************************************
		 * Function call
		 ***********************************************************************/
		case OPCODE_fa: // $FcnApply f[1]
		{
			TLAType domType;
			ExprOrOpArgNode dom = n.getArgs()[1];
			if (dom instanceof OpApplNode
					&& ((OpApplNode) dom).getOperator().getName().toString()
							.equals("$Tuple")) {
				ArrayList<TLAType> domList = new ArrayList<TLAType>();
				OpApplNode domOpAppl = (OpApplNode) dom;
				for (int i = 0; i < domOpAppl.getArgs().length; i++) {
					TLAType d = visitExprOrOpArgNode(domOpAppl.getArgs()[i],
							new Untyped());
					domList.add(d);
				}
				domType = new TupleType(domList);
			} else {
				domType = visitExprOrOpArgNode(n.getArgs()[1], new Untyped());
			}
			FunctionType func = new FunctionType(domType, expected);
			FunctionType res = (FunctionType) visitExprOrOpArgNode(
					n.getArgs()[0], func);
			return res.getRange();
		}

		/***********************************************************************
		 * Domain of Function
		 ***********************************************************************/
		case OPCODE_domain: {

			FunctionType func = new FunctionType(new Untyped(), new Untyped());
			func = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], func);
			TLAType res = null;
			try {
				res = new SetType(func.getDomain()).unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected '%s', found '%s' at 'DOMAIN(..)',\n%s",
						expected, n.getLocation()));
			}
			return res;
		}
		/***********************************************************************
		 * Set of Function
		 ***********************************************************************/
		case OPCODE_sof: // [ A -> B]
		{
			SetType A = (SetType) visitExprOrOpArgNode(n.getArgs()[0],
					new SetType(new Untyped()));
			SetType B = (SetType) visitExprOrOpArgNode(n.getArgs()[1],
					new SetType(new Untyped()));

			SetType found = new SetType(new FunctionType(A.getSubType(),
					B.getSubType()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected '%s', found '%s' at Set of Function,\n%s",
						expected, found, n.getLocation()));
			}
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
			ArrayList<TLAType> list = new ArrayList<TLAType>();
			for (int i = 0; i < n.getArgs().length; i++) {
				SetType t = (SetType) visitExprOrOpArgNode(n.getArgs()[i],
						new SetType(new Untyped()));
				list.add(t.getSubType());
			}

			SetType found = new SetType(new TupleType(list));
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
				SetType fieldType = (SetType) visitExprOrOpArgNode(
						pair.getArgs()[1], new SetType(new Untyped()));
				struct.add(field.getRep().toString(), fieldType.getSubType());
			}

			SetType found = new SetType(struct);
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
				TLAType fieldType = visitExprOrOpArgNode(pair.getArgs()[1],
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
			TLAType then = visitExprOrOpArgNode(n.getArgs()[1], expected);
			TLAType eelse = visitExprOrOpArgNode(n.getArgs()[2], then);
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
			TLAType found = expected;
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
			SetType S = (SetType) visitExprNode(bounds[0], new SetType(
					new Untyped()));
			TLAType found = S.getSubType();

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

	private TLAType evalBoundedVariables(OpApplNode n) throws TLA2BException {
		ArrayList<TLAType> domList = new ArrayList<TLAType>();
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] bounds = n.getBdedQuantBounds();
		for (int i = 0; i < bounds.length; i++) {
			SetType boundType = (SetType) visitExprNode(bounds[i], new SetType(
					new Untyped()));
			TLAType subType = boundType.getSubType();

			if (n.isBdedQuantATuple()[i]) {
				if (subType instanceof TupleType) {
					domList.add(subType);
					TupleType t = (TupleType) subType;
					if (params[i].length != t.getTypes().size()) {
						throw new TypeErrorException("Expected tuple with "
								+ params[i].length
								+ " components, found tuple with "
								+ t.getTypes().size() + " components.\n"
								+ bounds[i].getLocation());
					}
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode p = params[i][j];
						TLAType paramType = t.getTypes().get(j);
						p.setToolObject(TYPE_ID, paramType);
						if (paramType instanceof AbstractHasFollowers) {
							((AbstractHasFollowers) paramType).addFollower(p);
						}
					}
				} else if (subType instanceof Untyped) {
					TupleType tuple = new TupleType(params[i].length);
					try {
						tuple = (TupleType) tuple.unify(subType);
					} catch (UnificationException e) {
						throw new TypeErrorException(String.format(
								"Expected %s, found %s ,\n%s", tuple, subType,
								n.getLocation()));
					}

					domList.add(tuple);
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode p = params[i][j];
						TLAType paramType = tuple.getTypes().get(j);
						p.setToolObject(TYPE_ID, paramType);
						if (paramType instanceof AbstractHasFollowers) {
							((AbstractHasFollowers) paramType).addFollower(p);
						}
					}

				} else {
					throw new TypeErrorException("Expected tuple, found '"
							+ subType + "'.\n" + bounds[i].getLocation());
				}
			} else {
				// is not a tuple: all parameter have the same type
				for (int j = 0; j < params[i].length; j++) {
					domList.add(subType);
					FormalParamNode p = params[i][j];
					p.setToolObject(TYPE_ID, subType);
					if (subType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) subType).addFollower(p);
					}
				}
			}
		}

		TLAType domType = null;
		if (domList.size() == 1) {
			domType = domList.get(0);
		} else {
			domType = new TupleType(domList);
		}
		return domType;
	}

	/**
	 * @param n
	 * @param expected
	 * @return
	 * @throws TLA2BException
	 */
	private TLAType evalExcept(OpApplNode n, TLAType expected)
			throws TLA2BException {
		TLAType t = visitExprOrOpArgNode(n.getArgs()[0], expected);
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
			TLAType valueType = visitExprOrOpArgNode(rightside, untyped);

			OpApplNode seq = (OpApplNode) leftside;
			LinkedList<ExprOrOpArgNode> list = new LinkedList<ExprOrOpArgNode>();
			for (int j = 0; j < seq.getArgs().length; j++) {
				list.add(seq.getArgs()[j]);
			}
			ExprOrOpArgNode first = list.poll();

			if (first instanceof StringNode) {
				String field = ((StringNode) first).getRep().toString();
				TLAType res = evalType(list, valueType);
				StructOrFunction s = new StructOrFunction(field, res);
				try {
					t = t.unify(s);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format(
							"Expected %s, found %s at 'EXCEPT',\n%s", t, s,
							pair.getLocation()));
				}

			} else {
				// Function
				ExprOrOpArgNode domExpr = first;
				TLAType domType;
				TLAType rangeType;
				if (domExpr instanceof OpApplNode
						&& ((OpApplNode) domExpr).getOperator().getName()
								.toString().equals("$Tuple")) {
					ArrayList<TLAType> domList = new ArrayList<TLAType>();
					OpApplNode domOpAppl = (OpApplNode) domExpr;
					for (int j = 0; j < domOpAppl.getArgs().length; j++) {
						TLAType d = visitExprOrOpArgNode(
								domOpAppl.getArgs()[j], new Untyped());
						domList.add(d);
					}
					domType = new TupleType(domList);
				} else {
					domType = visitExprOrOpArgNode(domExpr, new Untyped());
				}
				rangeType = evalType(list, valueType);
				FunctionType func = new FunctionType(domType, rangeType);
				try {
					t = t.unify(func);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format(
							"Expected %s, found %s at 'EXCEPT',\n%s", t, func,
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
	private TLAType evalType(LinkedList<ExprOrOpArgNode> list, TLAType valueType)
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
		TLAType t = visitExprOrOpArgNode(head, new Untyped());
		FunctionType res = new FunctionType(t, evalType(list, valueType));
		return res;
	}

	private TLAType evalBBuiltIns(OpApplNode n, TLAType expected)
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
				expected.unify(new SetType(IntType.getInstance()));
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER) at '..',\n%s",
						expected, n.getLocation()));
			}

			for (int i = 0; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], IntType.getInstance());
			}
			return new SetType(IntType.getInstance());
		}

		case B_OPCODE_nat: // Nat
		{
			try {
				SetType found = new SetType(IntType.getInstance());
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
				SetType found = new SetType(IntType.getInstance());
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
			visitExprOrOpArgNode(n.getArgs()[0], new SetType(new Untyped()));
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
			visitExprOrOpArgNode(n.getArgs()[0], new SetType(new Untyped()));
			return IntType.getInstance();
		}

		/**********************************************************************
		 * Standard Module Sequences
		 **********************************************************************/
		case B_OPCODE_seq: { // Seq(S) - set of sequences, S must be a set

			SetType S = (SetType) visitExprOrOpArgNode(n.getArgs()[0],
					new SetType(new Untyped()));

			SetType set_of_seq = new SetType(new FunctionType(
					IntType.getInstance(), S.getSubType()));
			try {
				set_of_seq = set_of_seq.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'Seq',\n%s", expected,
						set_of_seq, n.getLocation()));
			}
			return set_of_seq;
		}

		case B_OPCODE_len: { // lengh of the sequence
			try {
				IntType.getInstance().unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found INTEGER at 'Len',\n%s", expected,
						n.getLocation()));
			}
			visitExprOrOpArgNode(n.getArgs()[0],
					new FunctionType(IntType.getInstance(), new Untyped()));
			return IntType.getInstance();
		}

		case B_OPCODE_conc: { // s \o s2 - concatenation of s and s2
			FunctionType found = new FunctionType(IntType.getInstance(),
					new Untyped());
			found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
			found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[1], found);
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(INTEGER*_A) at '\\o',\n%s",
						expected, n.getLocation()));
			}
			return found;
		}

		case B_OPCODE_append: // Append(s, e)
		{
			FunctionType found = new FunctionType(IntType.getInstance(),
					new Untyped());
			found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
			visitExprOrOpArgNode(n.getArgs()[1], found.getRange());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'Append',\n%s", expected,
						found, n.getLocation()));
			}
			return found;
		}

		case B_OPCODE_head: { // HEAD(s) - the first element of the sequence
			FunctionType func = new FunctionType(IntType.getInstance(),
					new Untyped());
			func = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], func);

			TLAType found = func.getRange();
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'Head',\n%s", expected,
						found, n.getLocation()));
			}
			return found;
		}

		case B_OPCODE_tail: { // Tail(s)
			FunctionType found = new FunctionType(IntType.getInstance(),
					new Untyped());
			found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'Tail',\n%s", expected,
						found, n.getLocation()));
			}
			return found;
		}

		case B_OPCODE_subseq: { // SubSeq(s,m,n)
			FunctionType found = new FunctionType(IntType.getInstance(),
					new Untyped());
			found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
			visitExprOrOpArgNode(n.getArgs()[1], IntType.getInstance());
			visitExprOrOpArgNode(n.getArgs()[2], IntType.getInstance());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'SubSeq',\n%s", expected,
						found, n.getLocation()));
			}
			return found;
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
					new SetType(IntType.getInstance()));
			return IntType.getInstance();
		}

		case B_OPCODE_permseq: { // PermutedSequences(S)
			SetType argType = (SetType) visitExprOrOpArgNode(n.getArgs()[0],
					new SetType(new Untyped()));
			SetType found = new SetType(new FunctionType(IntType.getInstance(),
					argType.getSubType()));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at 'PermutedSequences',\n%s",
						expected, found, n.getLocation()));
			}
			return found;
		}

		/**********************************************************************
		 * Standard Module TLA2B
		 **********************************************************************/
		case B_OPCODE_pow1: // POW1
		{

			SetType set = new SetType(new Untyped());
			set = (SetType) visitExprOrOpArgNode(n.getArgs()[0], set);
			SetType found = new SetType(set);
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at '%s',\n%s", expected, n
								.getOperator().getName(), n.getLocation()));
			}
			return found;
		}

		/**********************************************************************
		 * Standard Module Relations
		 **********************************************************************/
		case B_OPCODE_rel_inverse: // POW1
		{
			SetType set = new SetType(new TupleType(2));
			set = (SetType) visitExprOrOpArgNode(n.getArgs()[0], set);
			TupleType t = (TupleType) set.getSubType();
			ArrayList<TLAType> list = new ArrayList<TLAType>();
			list.add(t.getTypes().get(1));
			list.add(t.getTypes().get(0));
			SetType found = new SetType(new TupleType(list));
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at '%s',\n%s", expected, found,
						n.getOperator().getName(), n.getLocation()));
			}
			return found;
		}

		/***********************************************************************
		 * TLA+ Built-Ins, but not in tlc.tool.BuiltInOPs
		 ***********************************************************************/
		case B_OPCODE_bool: // BOOLEAN
			try {
				SetType found = new SetType(BoolType.getInstance());
				found = found.unify(expected);
				return found;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(BOOL) at 'BOOLEAN',\n%s",
						expected, n.getLocation()));
			}

		case B_OPCODE_string: // STRING
			try {
				SetType found = new SetType(StringType.getInstance());
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

	public static TLAType makePair(ArrayList<TLAType> list) {
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

}
