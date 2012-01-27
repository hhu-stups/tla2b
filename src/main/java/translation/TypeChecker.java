/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;

import exceptions.MyException;
import exceptions.NotImplementedException;
import exceptions.TypeErrorException;
import exceptions.UnificationException;
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
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import types.*;
import util.StandardModules;

public class TypeChecker extends BuiltInOPs implements IType, ASTConstants,
		BBuildIns, TranslationGlobals {

	private final int TYPE_ID;
	private final int tempId;
	private int paramId;

	private ModuleNode root;
	private ModuleContext moduleContext;

	// MContext moduleContext;

	public TypeChecker(ModuleNode n, ModuleContext moduleContext) {
		this.moduleContext = moduleContext;
		root = n;
		TYPE_ID = 5;// FrontEnd.getToolId();
		tempId = 6;
		paramId = TYPE_ID;
	}

	public int getToolId() {
		return TYPE_ID;
	}

	public void start() throws MyException {
		visitModule(root);
	}

	private void visitModule(ModuleNode n) throws MyException {
		OpDeclNode[] cons = n.getConstantDecls();

		for (int i = 0; i < cons.length; i++) {
			OpDeclNode con = cons[i];
			String conName = con.getName().toString();
			if (moduleContext.conObjs != null
					&& moduleContext.conObjs.get(conName) != null) {
				BType t = moduleContext.conObjs.get(conName).getType();
				con.setToolObject(TYPE_ID, t);
			} else {
				Untyped u = new Untyped();
				con.setToolObject(TYPE_ID, u);
				u.addFollower(con);
			}
		}

		OpDeclNode[] vars = n.getVariableDecls();
		for (int i = 0; i < vars.length; i++) {
			OpDeclNode var = vars[i];
			Untyped u = new Untyped();
			var.setToolObject(TYPE_ID, u);
			u.addFollower(var);
		}

		evalDefinitions(n.getOpDefs());
		evalAssumptions(n.getAssumptions());
		if (moduleContext.next != null) {
			visitExprNode(moduleContext.next, BoolType.getInstance());
		}

		for (int i = 0; i < moduleContext.inits.size(); i++) {
			visitExprNode(moduleContext.inits.get(i).getNode(),
					BoolType.getInstance());
		}

		evalOverrides(n.getConstantDecls());

		for (int i = 0; i < vars.length; i++) {
			OpDeclNode var = vars[i];
			BType varType = (BType) var.getToolObject(TYPE_ID);
			if (varType.isUntyped()) {
				throw new TypeErrorException("Variable " + var.getName()
						+ " has no Type");
			}
		}

		for (int i = 0; i < cons.length; i++) {
			OpDeclNode con = cons[i];
			BType conType = (BType) con.getToolObject(TYPE_ID);
			if (conType.isUntyped()) {
				throw new TypeErrorException("The type of Constant "
						+ con.getName() + " is still untyped: " + conType);
			}
		}

		evalRecList();
	}

	/**
	 * 
	 */
	private void evalRecList() {
		for (int i = 0; i < moduleContext.recList.size(); i++) {
			OpApplNode n = moduleContext.recList.get(i);
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
				if(!fieldNames.contains(fieldName)&& struct.getType(fieldName).getKind()==MODELVALUE){
					EnumType e = (EnumType) struct.getType(fieldName);
					e.setNoVal();
				}
			}
		}
		
	}

	private void evalOverrides(OpDeclNode[] cons) throws UnificationException,
			TypeErrorException {
		if (moduleContext.getOverrides() == null) {
			return;
		}

		Hashtable<String, String> overrides = moduleContext.getOverrides();
		Hashtable<String, OpDeclNode> moduleCons = new Hashtable<String, OpDeclNode>();
		for (int i = 0; i < cons.length; i++) {
			moduleCons.put(cons[i].getName().toString(), cons[i]);
		}

		Iterator<Map.Entry<String, String>> it = overrides.entrySet()
				.iterator();
		while (it.hasNext()) {
			Map.Entry<String, String> entry = it.next();
			String left = entry.getKey();
			String right = entry.getValue();
			BType leftType = new Untyped();
			OpDefNode rightDef = moduleContext.definitions.get(right);
			BType rightType = (BType) rightDef.getToolObject(TYPE_ID);
			if (moduleCons.containsKey(left)) {
				OpDeclNode leftCon = moduleCons.get(left);
				leftType = (BType) leftCon.getToolObject(TYPE_ID);
			} else if (moduleContext.definitions.containsKey(left)) {
				OpDefNode leftDef = moduleContext.definitions.get(left);
				leftType = (BType) leftDef.getToolObject(TYPE_ID);
			}
			try {
				leftType.unify(rightType);
			} catch (UnificationException e) {
				throw new TypeErrorException(
						String.format(
								"Expected %s, found %s at '%s' (overriding symbol %s),\n%s ",
								leftType, rightType, rightDef.getName()
										.toString(), left, rightDef
										.getLocation()));
			}

		}
	}

	private void evalDefinitions(OpDefNode[] opDefs) throws MyException {
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
			Boolean usedDefintion = (Boolean) def
					.getToolObject(PRINT_DEFINITION);
			if (usedDefintion != null) {
				visitOpDefNode(def);
			}

		}

	}

	/**
	 * @param def
	 * @throws MyException
	 */
	private void visitOpDefNode(OpDefNode def) throws MyException {
		ConstantObj conObj = (ConstantObj) def.getToolObject(CONSTANT_OBJECT);
		if (conObj != null) {
			def.setToolObject(TYPE_ID, conObj.getType());
			if (conObj.getType() instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) conObj.getType()).addFollower(def);
			}
			return;
		}
		FormalParamNode[] params = def.getParams();
		for (int i = 0; i < params.length; i++) {
			FormalParamNode p = params[i];
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

	private void evalAssumptions(AssumeNode[] assumptions) throws MyException {
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
			throws MyException {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, expected);
		} else {
			throw new NotImplementedException("OpArgNode not implemented jet");
		}

	}

	private BType visitExprNode(ExprNode exprNode, BType expected)
			throws MyException {

		switch (exprNode.getKind()) {
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
		case AtNodeKind: // @
		{
			AtNode a = (AtNode) exprNode;
			BType base = visitExprNode(a.getAtBase(), new Untyped());
			if (base.getKind() == STRUCT) {
				StructType baseStruct = (StructType) base;
				OpApplNode seq = (OpApplNode) a.getAtModifier();
				StringNode sn = (StringNode) seq.getArgs()[0];
				String field = sn.getRep().toString();
				StructType struct = new StructType();
				struct.add(field, expected);
				try {
					struct = struct.unify(baseStruct);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format(
							"Expected %s, found %s at '@',\n%s ", expected,
							baseStruct.getType(field), exprNode.getLocation()));
				}
				return struct.getType(field);
			} else { // function
				PowerSetType found = new PowerSetType(new PairType());
				found = found.unify(base);
				PairType pair = (PairType) found.getSubType();
				BType res = new Untyped();
				try {
					res = pair.getSecond().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException("Can not unify "
							+ pair.getSecond() + " and " + expected + "\n"
							+ a.getLocation());
				}
				return res;
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
			SubstInNode substNode = (SubstInNode) exprNode;
			Subst[] subs = substNode.getSubsts();
			for (int i = 0; i < subs.length; i++) {
				Subst sub = subs[i];
				OpDeclNode op = sub.getOp();
				ExprOrOpArgNode expr = sub.getExpr();
				if (op.getLevel() == 1) {
					try {
						OpApplNode o = (OpApplNode) expr;
						@SuppressWarnings("unused")
						OpDeclNode var = (OpDeclNode) o.getOperator();
					} catch (Exception e) {
						throw new TypeErrorException(String.format(
								"Expected variable.\n%s ", expr.getLocation()));
					}
				}
				BType exprType;
				if (expr instanceof OpArgNode) {
					OpArgNode opArgNode = (OpArgNode) expr;
					exprType = (BType) opArgNode.getOp().getToolObject(TYPE_ID);
					if (exprType == null)
						exprType = new Untyped();
				} else {
					exprType = visitExprOrOpArgNode(expr, new Untyped());
				}
				op.setToolObject(TYPE_ID, exprType);
				if (exprType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) exprType).addFollower(op);
				}
			}

			return visitExprNode(substNode.getBody(), expected);// visitExprNode(substNode.getBody(),
			// expected);
		}

		}

		throw new NotImplementedException(exprNode.toString(2));

	}

	/**
	 * @param n
	 * @param expected
	 * @return {@link BType}
	 * @throws MyException
	 */
	private BType visitOpApplNode(OpApplNode n, BType expected)
			throws MyException {
		SymbolNode symbolNode = n.getOperator();
		switch (symbolNode.getKind()) {
		case ConstantDeclKind: {
			String cName = symbolNode.getName().toString();
			BType c = (BType) symbolNode.getToolObject(TYPE_ID);
			if (c == null) {
				throw new RuntimeException(cName + " has no type yet!");
			}
			try {
				BType result = expected.unify(c);
				symbolNode.setToolObject(TYPE_ID, result);
				return result;
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found %s at constant '%s',\n%s",
						expected, c, cName, n.getLocation())

				);
			}
		}

		case VariableDeclKind: {
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
			// Definition is a BBuilt-in definition
			if (BBuiltInOPs.contains(n.getOperator().getName())) {
				return evalBBuiltIns(n, expected);
			}
			OpDefNode def = (OpDefNode) n.getOperator();
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

			FormalParamNode[] params = def.getParams();
			for (int i = 0; i < n.getArgs().length; i++) {
				// clone the parameter type, because the parameter type is not
				// set/changed at
				// a definition call
				FormalParamNode p = params[i];
				BType pType = ((BType) p.getToolObject(TYPE_ID));
				if (pType == null) {
					pType = new Untyped();
					// throw new RuntimeException("Parameter " + p.getName()
					// + " has no type yet!\n" + p.getLocation());
				}

				pType = pType.cloneBType();
				pType = visitExprOrOpArgNode(n.getArgs()[i], pType);
				// set types of the arguments of the definition call to the
				// parameters (position paramID+1) for reevaluation the def body
				p.setToolObject(tempId, pType);
			}

			if (def.getToolObject(CONSTANT_OBJECT) == null) {
				// evaluate the body of the definition again
				paramId = tempId;
				found = visitExprNode(def.getBody(), found);
				paramId = TYPE_ID;
			}

			n.setToolObject(TYPE_ID, found);

			return found;

		}

		default: {
			throw new NotImplementedException(symbolNode.getName().toString());
		}
		}

	}

	private BType evalBBuiltIns(OpApplNode n, BType expected)
			throws MyException {
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
		case B_OPCODE_exp: // x hoch y, x^y
		{
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
						"Expected %s, found POW(INTEGER) at '%s',\n%s",
						expected, n.getOperator().getName(), n.getLocation()));
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

	/**
	 * @param exprNode
	 * @param expected
	 * @return {@link BType}
	 * @throws MyException
	 */
	private BType evalBuiltInKind(OpApplNode n, BType expected)
			throws MyException {

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
			BType t = visitExprOrOpArgNode(n.getArgs()[0], expected);
			n.setToolObject(TYPE_ID, t);
			if (t instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) t).addFollower(n);
			}
			// Struct
			if (t instanceof StructType) {
				StructType struct = new StructType();
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					OpApplNode seq = (OpApplNode) pair.getArgs()[0];
					if (seq.getArgs().length > 1) {
						throw new TypeErrorException(
								String.format(
										"Fields of Field are not supported in 'EXCEPT' clause.\n%s",
										seq.getLocation()));
					}
					StringNode sn;
					try {
						sn = (StringNode) seq.getArgs()[0];
					} catch (ClassCastException e) {
						throw new TypeErrorException(String.format(
								"Expected field name.\n%s",
								seq.getArgs()[0].getLocation()));
					}
					String field = sn.getRep().toString();
					BType fieldType = visitExprOrOpArgNode(pair.getArgs()[1],
							new Untyped());
					struct.add(field, fieldType);
				}
				return visitExprOrOpArgNode(n.getArgs()[0], struct);
			}

			// function
			PowerSetType found = new PowerSetType(new PairType());
			try {
				found = found.unify(expected);
			} catch (UnificationException e) {
				throw new TypeErrorException(String.format(
						"Expected %s, found POW(_A*_B) at Except,\n%s",
						expected, n.getArgs()[0].getLocation()));
			}
			found = (PowerSetType) visitExprOrOpArgNode(n.getArgs()[0], found);

			PairType found_pair = (PairType) found.getSubType();
			BType domType = found_pair.getFirst();
			BType rangeType = found_pair.getSecond();
			for (int i = 1; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i]; // Pair
				// domain
				OpApplNode domSeq = (OpApplNode) pair.getArgs()[0];
				if (domSeq.getArgs().length > 1) {
					throw new TypeErrorException(
							String.format(
									"Multidimensional functions like 'f[x][y]' are not supported.\n%s",
									domSeq.getLocation()));
				}
				ExprOrOpArgNode domExpr = domSeq.getArgs()[0];
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
					try {
						domType = domType.unify(makePair(domList));
					} catch (UnificationException e) {
						throw new TypeErrorException(String.format(
								"Expected %s, found %s at Except,\n%s",
								domType, makePair(domList),
								domOpAppl.getLocation()));
					}
				} else {
					domType = visitExprOrOpArgNode(domExpr, domType);
				}
				// range
				rangeType = visitExprOrOpArgNode(pair.getArgs()[1], rangeType);
			}

			return found;
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
			moduleContext.recList.add(n);
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
	 * @throws MyException
	 */
	private void evalBoundedVariables(OpApplNode n) throws MyException {
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
