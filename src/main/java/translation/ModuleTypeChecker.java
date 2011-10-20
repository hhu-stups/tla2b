package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

import exceptions.ModuleErrorException;
import exceptions.MyException;
import exceptions.NotImplementedException;
import exceptions.TypeErrorException;

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
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tlc2.tool.BuiltInOPs;
import types.*;

// typechecking and typinference
public class ModuleTypeChecker extends BuiltInOPs implements ASTConstants,
		IType, BBuildIns {
	private ModuleNode root;
	private Hashtable<String, Constant> constants;
	private Hashtable<String, Variable> variables;
	private Hashtable<String, DefContext> definitions;
	private ModuleContext moduleContext;

	public Hashtable<String, Constant> getConstants() {
		return constants;
	}

	public Hashtable<String, Variable> getVariables() {
		return variables;
	}

	public Hashtable<String, DefContext> getDefinitions() {
		return definitions;
	}

	public ModuleTypeChecker(ModuleNode n, ModuleContext mc) {
		root = n;
		constants = mc.getConstants();
		moduleContext = mc;
		definitions = new Hashtable<String, DefContext>();

	}

	public ModuleTypeChecker(ModuleNode n) {
		root = n;
	}

	public void start() throws MyException {
		visitModule(root);

		moduleContext.constants = getConstants();
		moduleContext.variables = getVariables();
		moduleContext.definitions = getDefinitions();

		if (moduleContext.variables.size() > 0
				&& moduleContext.getInit().equals("")) {
			throw new ModuleErrorException("No initialisation predicate.");
		}
	}

	private void evalOverrides() throws MyException {
		Enumeration<String> keys = moduleContext.overrides.keys();
		Enumeration<String> values = moduleContext.overrides.elements();
		while (keys.hasMoreElements()) {
			Constant c = constants.get(keys.nextElement());
			MyType t1 = c.getType();
			MyType t2 = definitions.get(values.nextElement()).getType();

			if (!t1.equals(t2)) {
				throw new TypeErrorException(
						"Configfile Typeerror for Constant " + c.getName()
								+ ": Expected " + t1 + " but was " + t2);
			}
			c.setType(t1.compare(t2));
		}

	}

	public void visitModule(ModuleNode n) throws MyException {
		// alle Variablen aus VARIABLES
		evalVariables(n.getVariableDecls());

		int counter = countUntypedVarsCons();
		int old = Integer.MAX_VALUE;
		int i = 0;

		while (i < 2 || counter < old) {
			old = counter;
			evalAssumptions(n.getAssumptions());
			evalDefinitions(n.getOpDefs());
			evalOverrides();
			counter = countUntypedVarsCons();
			i++;
		}
		if (counter > 0) {
			Enumeration<Variable> e = variables.elements();
			while (e.hasMoreElements()) {
				Variable var = e.nextElement();
				if (var.getType().isUntyped()) {
					throw new TypeErrorException("Variable " + var.getName()
							+ " has no Type");
				}
			}
			Enumeration<Constant> c = constants.elements();
			while (c.hasMoreElements()) {
				Constant con = c.nextElement();
				if (con.getType().isUntyped()) {
					throw new TypeErrorException("Constant " + con.getName()
							+ " has no Type");
				}
			}
		}

	}

	// Assumptions
	private void evalAssumptions(AssumeNode[] assumptions) throws MyException {

		for (AssumeNode assumeNode : assumptions) {
			DefContext d = new DefContext();
			visitExprNode(assumeNode.getAssume(), d, new BooleanType());
			assumeNode.setToolObject(1, d);
		}
	}

	// Helper Method: Counts the number of Untyped Variables
	private int countUntypedVarsCons() {
		Enumeration<Variable> e = variables.elements();
		int counter = 0;
		while (e.hasMoreElements()) {
			Variable var = e.nextElement();
			if (var.getType().isUntyped()) {
				counter++;
			}
		}
		Enumeration<Constant> c = constants.elements();
		while (c.hasMoreElements()) {
			Constant con = c.nextElement();
			if (con.getType().isUntyped()) {
				counter++;
			}
		}
		return counter;
	}

	private void evalVariables(OpDeclNode[] vars) {
		variables = new Hashtable<String, Variable>();
		if (vars.length > 0) {
			for (int i = 0; i < vars.length; i++) {
				String var = vars[i].getName().toString();
				variables.put(var, new Variable(var, new Untyped()));
			}

		}
	}

	private void evalDefinitions(OpDefNode[] opDefs) throws MyException {
		ArrayList<String> standardModules = new ArrayList<String>();
		standardModules.add("TLC");
		standardModules.add("Naturals");
		standardModules.add("FiniteSets");
		standardModules.add("Sequences");
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
			// Definition in this module

			if (!standardModules.contains(def
					.getOriginallyDefinedInModuleNode().getName().toString())) {
				visitOpDefNode(def);
			}
		}
	}

	// Definitions
	public void visitOpDefNode(OpDefNode n) throws MyException {
		String defName = n.getName().toString();
		DefContext d;
		MyType expected = new Untyped();
		if (defName.equals(moduleContext.getInit())
				|| defName.equals(moduleContext.getNext())) {
			expected = new BooleanType();
		}
		if (definitions.get(defName) == null) {
			// first time
			d = new DefContext(defName);
			d.setParams(evalParams(n.getParams()));

			String prefix = null;
			if (defName.contains("!")) {
				prefix = defName.substring(0, defName.lastIndexOf('!'));
			}
			d.setPrefix(prefix);

			MyType t = visitExprNode(n.getBody(), d, expected);
			d.setType(t);
			if (t.getType() != BOOLEAN) {
				d.setEquation(true);
			}
			definitions.put(defName, d);
		} else {
			d = definitions.get(defName);
			MyType t = visitExprNode(n.getBody(), d, expected);
			d.setType(t);
		}

	}

	private String[] evalParams(FormalParamNode[] params) {
		String[] res = new String[params.length];
		for (int i = 0; i < params.length; i++) {
			res[i] = params[i].getName().toString();
		}
		return res;
	}

	public MyType visitExprNode(ExprNode n, DefContext c, MyType expected)
			throws MyException {
		switch (n.getKind()) {
		case OpApplKind:
			return visitOpApplNode((OpApplNode) n, c, expected);

		case NumeralKind:
			compareTypes(n, "" + ((NumeralNode) n).val(), expected,
					new IntType());
			return new IntType();
		case StringKind:
			compareTypes(n, "" + ((StringNode) n).getRep(), expected,
					new StringType());
			return new StringType();

		case AtNodeKind: // @
			AtNode a = (AtNode) n;

			MyType pp = visitExprNode(a.getAtBase(), c, null);
			if (pp.getType() == UNTYPED) {
				return new Untyped();
			}
			if (pp.getType() == STRUCT) {
				StructType s = (StructType) pp;

				OpApplNode seq = (OpApplNode) a.getAtModifier();
				StringNode sn = (StringNode) seq.getArgs()[0];
				String name = sn.getRep().toString();
				if (!s.names.contains(name)) {
					throw new TypeErrorException(pp
							+ " does not contain identifier" + name + "\n"
							+ sn.getLocation());
				}
				MyType temp = s.types.get(s.names.indexOf(name));
				compareTypes(n, "@", expected, temp);
				return temp;

			} else if (pp.getType() == POW) {
				// a.getAtModifier()
				PowerSetType p = (PowerSetType) pp;
				PairType pair = (PairType) p.getSubType();
				return pair.getSecond();
			} else
				return null;

		case LetInKind: {
			LetInNode l = (LetInNode) n;
			for (int i = 0; i < l.getLets().length; i++) {
				OpDefNode def = l.getLets()[i];
				String defname = def.getName().toString();
				DefContext d;
				if (c.lets.get(defname) == null) {
					// erster Durchlauf
					d = new DefContext(defname);
					d.setParams(evalParams(def.getParams()));
					// alle Parameter aus der umgebenen Definition
					d.temp.putAll(c.parameters);
					d.temp.putAll(c.temp);
					d.lets.putAll(c.lets);
					// d.parameters.putAll(c.parameters);

					// eval Body
					MyType t = visitExprNode(def.getBody(), d, new Untyped());
					d.setType(t);

					// TODO ???
					if (t.getType() != BOOLEAN) {
						d.setEquation(true);
					}
					c.lets.put(defname, new Subdefinition(d, def));

				} else {
					// weiterer Durchlauf
					d = c.lets.get(defname).getDefCon();
					MyType t = visitExprNode(def.getBody(), d, d.getType());
					d.setType(t);
				}
			}

			// let Body
			return visitExprNode(l.getBody(), c, expected);
		}

		case SubstInKind: {
			SubstInNode substNode = (SubstInNode) n;
			Subst[] subs = substNode.getSubsts();
			for (int i = 0; i < subs.length; i++) {
				// eliminate substitutions like x <- x
				if (subs[i].getExpr().getKind() == OpApplKind) {
					OpApplNode o = (OpApplNode) subs[i].getExpr();
					if (o.getOperator().getName().toString() == subs[i].getOp()
							.getName().toString()) {
						continue;
					}
				}

				c.substitution.put(subs[i].getOp().getName().toString(),
						subs[i].getExpr());

			}
			return visitExprNode(substNode.getBody(), c, expected);
		}

		default:
			throw new NotImplementedException("unknown ExprNode" + n.getKind());
		}
	}

	public MyType visitOpApplNode(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind:
			String cName = n.getOperator().getName().toString();

			if (c.substitution.containsKey(cName)) {
				return visitExprOrOpArgNode(c.substitution.get(cName), c,
						expected);
			}

			Constant con = constants.get(cName);
			compareTypes(n, cName, expected, con.getType());
			if (expected == null) {
				return con.getType();

			} else {
				con.setType(expected.compare(con.getType()));
				return expected.compare(con.getType());
			}

		case VariableDeclKind: // Bezeichner im Module
		{
			String vName = n.getOperator().getName().toString();

			if (c.substitution.containsKey(vName)) {
				return visitExprOrOpArgNode(c.substitution.get(vName), c,
						expected);
			}
			Variable v = variables.get(vName);
			compareTypes(n, vName, expected, v.getType());
			if (expected != null) {
				v.setType(expected.compare(v.getType()));
				return expected.compare(v.getType());
			} else
				return v.getType();
		}

		case UserDefinedOpKind:
			if (BBuiltInOPs.contains(n.getOperator().getName())) {
				return evalBBuiltIns(n, c, expected);
			}

			return evalUserDefinedOpKind(n, c, expected);

		case BuiltInKind:
			return evalBuiltInKind(n, c, expected);

		case FormalParamKind:
			String name = n.getOperator().getName().toString();
			if (c.parameters.containsKey(name)) {
				Parameter p = c.parameters.get(name);
				MyType t = p.getType();

				MyType res = t.compare(expected);
				if (res == null) {
					throw new TypeErrorException("Expected " + expected
							+ ", found " + t + " in " + name + "\n"
							+ n.getLocation());
				}
				p.setType(res);
				return res;

			} else {
				Parameter p = c.temp.get(name);
				MyType t = p.getType();

				MyType res = t.compare(expected);
				if (res == null) {
					throw new TypeErrorException("Expected " + expected
							+ ", found " + t + " in " + name + "\n"
							+ n.getLocation());
				}

				p.setType(res);
				n.setToolObject(0, p);

				return res;
			}

		default:
			throw new NotImplementedException("unknown OppAppl-Typ "
					+ n.getOperator().getName());
		}

	}

	private MyType evalBBuiltIns(OpApplNode n, DefContext c, MyType expected)
			throws MyException {

		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {
		// B Builtins

		// Standart Module Naturals
		case B_OPCODE_dotdot: // ..
			evalOpMoreArgs(n, expected, new PowerSetType(new IntType()),
					new IntType(), c);
			return new PowerSetType(new IntType());

		case B_OPCODE_gt: // >
		case B_OPCODE_lt: // <
		case B_OPCODE_leq: // <=
		case B_OPCODE_geq: // >=
			evalOpMoreArgs(n, expected, new BooleanType(), new IntType(), c);
			return new BooleanType();

		case B_OPCODE_plus: // +
		case B_OPCODE_minus: // -
		case B_OPCODE_times: // *
		case B_OPCODE_div: // /
		case B_OPCODE_mod: // % modulo
		case B_OPCODE_exp: // x hoch y, x^y
			evalOpMoreArgs(n, expected, new IntType(), new IntType(), c);
			return new IntType();

		case B_OPCODE_nat: // Nat
			compareTypes(n, "Nat", expected, new PowerSetType(new IntType()));
			return new PowerSetType(new IntType());

			// Standart Module Integers
		case B_OPCODE_int: // Int
			compareTypes(n, "Int", expected, new PowerSetType(new IntType()));
			return new PowerSetType(new IntType());
		case B_OPCODE_uminus: // -x
			visitExprOrOpArgNode(n.getArgs()[0], c, new IntType());
			return new IntType();

			// Standart Module FiniteSets
		case B_OPCODE_finite: // IsFiniteSet
			compareTypes(n, "IsFiniteSet", expected, new BooleanType());
			visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(
					new Untyped()));
			return new BooleanType();

		case B_OPCODE_card: // Cardinality
			compareTypes(n, "Cardinality", expected, new IntType());
			visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(
					new Untyped()));
			return new IntType();

			// Standart Module Sequences
		case B_OPCODE_len:
			compareTypes(n, "len", expected, new IntType());
			visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(
					new PairType(new IntType(), new Untyped())));
			return new IntType();

		case B_OPCODE_append: {
			MyType sq = new PowerSetType(new PairType(new IntType(),
					new Untyped()));
			compareTypes(n, "append", expected, sq);

			MyType t = expected != null ? expected.compare(sq) : sq;

			MyType t2 = visitExprOrOpArgNode(n.getArgs()[0], c, t);

			MyType t3 = ((PairType) ((PowerSetType) t2).getSubType())
					.getSecond();
			visitExprOrOpArgNode(n.getArgs()[1], c, t3);
			return t2;
		}

		case B_OPCODE_seq: { // Seq(S) - set of sequences, S must be a set

			MyType set_of_seq = new PowerSetType(new PowerSetType(new PairType(
					new IntType(), new Untyped())));
			MyType compare = set_of_seq.compare(expected);
			PowerSetType seq = (PowerSetType) ((PowerSetType) compare)
					.getSubType();
			PairType pair = (PairType) seq.getSubType();

			PowerSetType set_elements = (PowerSetType) visitExprOrOpArgNode(
					n.getArgs()[0], c, new PowerSetType(pair.getSecond()));

			MyType res = new PowerSetType(new PowerSetType(new PairType(
					new IntType(), set_elements.getSubType())));
			return res;
		}

		case B_OPCODE_head: // HEAD(s) - the first element of the sequence
		{
			PowerSetType t = new PowerSetType(new PairType(new IntType(),
					expected));
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c, t);
			return ((PairType) ((PowerSetType) res).getSubType()).getSecond();

		}

		case B_OPCODE_tail: // Tail(s)
		{
			MyType t = new PowerSetType(new PairType(new IntType(),
					new Untyped())).compare(expected);
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c, t);
			return res;

		}

		case B_OPCODE_conc: // s \o s2 - concatenation of s and s2
		{
			MyType t = new PowerSetType(new PairType(new IntType(),
					new Untyped())).compare(expected);
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c, t);
			MyType res2 = visitExprOrOpArgNode(n.getArgs()[0], c, res);
			visitExprOrOpArgNode(n.getArgs()[0], c, res2);
			return res2;
		}

		case B_OPCODE_subseq: // SubSeq(s,m,n)
		{

			MyType t = new PowerSetType(new PairType(new IntType(),
					new Untyped())).compare(expected);
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c, t);

			visitExprOrOpArgNode(n.getArgs()[1], c, new IntType());
			visitExprOrOpArgNode(n.getArgs()[2], c, new IntType());

			return res;
		}

		// TLA Builtins, but not in tlc.tool.BuiltInOPs
		case B_OPCODE_bool: // BOOLEAN
			compareTypes(n, "BOOLEAN", expected, new PowerSetType(
					new BooleanType()));
			return new PowerSetType(new BooleanType());

		case B_OPCODE_string: // STRING
			return new PowerSetType(new StringType());

		case B_OPCODE_true:
		case B_OPCODE_false:
			compareTypes(n, n.getOperator().getName().toString(), expected,
					new BooleanType());
			return new BooleanType(false);

		default:
			throw new NotImplementedException(
					"Typecheck: B Builtin not implemented: "
							+ n.getOperator().getName());
		}

	}

	private MyType evalUserDefinedOpKind(OpApplNode n, DefContext c,
			MyType expected) throws MyException {

		// Operator ist ein B-BuiltIn-Operator
		if (BBuiltInOPs.contains(n.getOperator().getName())) {
			return evalBBuiltIns(n, c, expected);
		}

		// Definition Call
		String name = n.getOperator().getName().toString();

		DefContext d = null;
		// definition is a Subdefinition
		if (c.lets.containsKey(name)) {
			d = c.lets.get(name).getDefCon();
		}
		// definition is a definition of instanced module
		else if (c.getPrefix() != null) {
			d = definitions.get(c.getPrefix() + "!" + name);
		}
		// definition is a normal definition 
		else {
			d = definitions.get(name);
		}

		if (d == null) {
			// TODO
			// System.err.println("subdefinition " + name +
			// " not evaluated yet");
			// Definitionen sind noch nicht ausgewertet
			return expected;
		}
		compareTypes(n, name, expected, d.getType());

		if (n.getArgs().length > 0) {
			String[] pNames = d.getParams();
			for (int i = 0; i < n.getArgs().length; i++) {
				MyType t = d.parameters.get(pNames[i]).getType();
				visitExprOrOpArgNode(n.getArgs()[i], c, t);
			}
		}
		return d.getType();
	}

	private MyType evalBuiltInKind(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		switch (getOpCode(n.getOperator().getName())) {
		case OPCODE_neg:
		case OPCODE_lnot:
		case OPCODE_cl: // $ConjList
		case OPCODE_dl: // $DisjList
		case OPCODE_land: // \land
		case OPCODE_lor: // \lor
		case OPCODE_equiv: // \equiv
		case OPCODE_implies: // =>
			evalOpMoreArgs(n, expected, new BooleanType(), new BooleanType(), c);
			return new BooleanType();

		case OPCODE_uc: // $UnboundedChoose
			return new Untyped();
		case OPCODE_bc:// $BoundedChoose
		{
			// n.setToolObject(0, "hallo");

			bounded(n, c);
			visitExprOrOpArgNode(n.getArgs()[0], c, new BooleanType());

			Parameter v = c.temp.get(n.getBdedQuantSymbolLists()[0][0]
					.getName().toString());
			return v.getType();
		}
		case OPCODE_in: // \in
		case OPCODE_notin: // \notin
			return evalElementof(n, c, expected);

		case OPCODE_prime: // prime
		{
			try {
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				if (node.getOperator().getKind() != VariableDeclKind) {
					throw new TypeErrorException("Expected variable at \""
							+ node.getOperator().getName() + "\":\n"
							+ node.getLocation());
				}
				return visitExprOrOpArgNode(n.getArgs()[0], c, expected);
			} catch (ClassCastException e) {
				throw new TypeErrorException(
						"Expected variable as argument of prime operator:\n"
								+ n.getArgs()[0].getLocation());
			}
		}

		case OPCODE_noteq: // /=
		case OPCODE_eq: // =
			evalOpEquals(n, c, expected);
			return new BooleanType();

		case OPCODE_ite: // IF THEN ELSE
		{
			visitExprOrOpArgNode(n.getArgs()[0], c, new BooleanType());
			MyType then = visitExprOrOpArgNode(n.getArgs()[1], c, expected);
			MyType eelse = visitExprOrOpArgNode(n.getArgs()[2], c, then);
			visitExprOrOpArgNode(n.getArgs()[1], c, eelse);
			n.setToolObject(1, eelse);
			return eelse;
		}

		case OPCODE_case: {
			MyType t = expected;
			int end = n.getArgs().length;
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				visitExprOrOpArgNode(pair.getArgs()[0], c, new BooleanType());
				if (t.isUntyped() == false)
					end = i;
				t = visitExprOrOpArgNode(pair.getArgs()[1], c, t);
			}

			for (int i = 0; i < end; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				visitExprOrOpArgNode(pair.getArgs()[1], c, t);
			}
			return t;
		}

		case OPCODE_subset: // SUBSET POW
		{
			compareTypes(n, "SUBSET", expected, new PowerSetType(new Untyped()));
			MyType t = null;
			t = new PowerSetType(new PowerSetType(new Untyped()))
					.compare(expected);
			if (t == null) {
				throw new TypeErrorException("Expected: " + expected
						+ ", found: POW(POW(...)\n" + n.getLocation());
			}
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c,
					((PowerSetType) t).getSubType());
			return new PowerSetType(res);
		}

		case OPCODE_se: // SetEnumeration {..}
			return evalSet(n, c, expected);

		case OPCODE_union: // Union
		{
			MyType res = visitExprOrOpArgNode(n.getArgs()[0], c,
					new PowerSetType(new PowerSetType(new Untyped())));
			return ((PowerSetType) res).getSubType();
		}
		case OPCODE_setdiff: // Setdifferenz
		case OPCODE_cup:
		case OPCODE_cap: // \intersect
			return evalSetOperator(n, c, expected);

		case OPCODE_subseteq: // \subseteq
			return evalSubset(n, c, expected);

			/*********** Function ****************/
		case OPCODE_nrfs: // succ[n \in Nat] == n + 1
		case OPCODE_fc: // [n \in Nat |-> n+1]
			return evalLambdaFc(n, c, expected);

		case OPCODE_fa: // $FcnApply f[1]
			return evalFunctionApply(n, c, expected);

		case OPCODE_sof: // [ A -> b]
			return evalSetOfFunction(n, c, expected);

		case OPCODE_domain: {
			MyType f = visitExprOrOpArgNode(n.getArgs()[0], c,
					new PowerSetType(new PairType()));
			MyType dom = ((PairType) ((PowerSetType) f).getSubType())
					.getFirst();
			return new PowerSetType(dom);
		}
		/************* End Function ********/

		case OPCODE_sso: // $SubsetOf Represents {x \in S : p}.
			return evalSubsetOf(n, c, expected);

		case OPCODE_soa: // $SetOfAll Represents {e : x \in S}. TODO translation
		{
			MyType e = new PowerSetType(new Untyped()).compare(expected);
			if (e == null) {
				throw new TypeErrorException("Expected " + expected
						+ ", found POW(_A)\n" + n.getLocation());
			}
			bounded(n, c);
			MyType t = visitExprOrOpArgNode(n.getArgs()[0], c,
					((PowerSetType) e).getSubType());
			return new PowerSetType(t);
		}

		case OPCODE_exc: // Except
			return evalExcept(n, c, expected);

		case OPCODE_pair: // val:Data oder ![2] = 2
			return evalPair(n, c, expected);

		case OPCODE_seq: // !
			return visitExprOrOpArgNode(n.getArgs()[0], c, expected);

		case OPCODE_rs: // $RcdSelect r.c
			return evalRcdSelect(n, c, expected);

		case OPCODE_tup: // $Tuple
			return evalTuple(n, c, expected);

		case OPCODE_cp: // $CartesianProd A \X B \X C as $CartesianProd(A, B, C)
		{
			MyType e = new PowerSetType(new PairType()).compare(expected);
			if (e == null) {
				throw new TypeErrorException("Expected" + e
						+ ", found POW(PAIR(_A,_B))\n" + n.getLocation());
			}
			PairType pair = (PairType) ((PowerSetType) e).getSubType();
			ArrayList<MyType> expectedList = pair.getList();
			ArrayList<MyType> a = new ArrayList<MyType>();
			for (int i = 0; i < n.getArgs().length; i++) {
				PowerSetType p = (PowerSetType) visitExprOrOpArgNode(
						n.getArgs()[i], c,
						new PowerSetType(expectedList.get(i)));
				a.add(p.getSubType());
			}
			return new PowerSetType(makePair(a));
		}

		// TODO Typechecking Records
		case OPCODE_rc: // [h_1 |-> 1, h_2 |-> 2]
		{
			StructType st = new StructType();
			for (int i = 0; i < n.getArgs().length; i++) {
				PairType arg = (PairType) visitExprOrOpArgNode(n.getArgs()[i],
						c, new Untyped());
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				StringNode field = (StringNode) pair.getArgs()[0];
				st.names.add(field.getRep().toString());
				st.types.add(arg.getSecond());
			}
			return st;
		}
		case OPCODE_sor: // $SetOfRcds [L1 : e1, L2 : e2]
			StructType st = new StructType();
			for (int i = 0; i < n.getArgs().length; i++) {
				PairType arg = (PairType) visitExprOrOpArgNode(n.getArgs()[i],
						c, new Untyped());
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				StringNode field = (StringNode) pair.getArgs()[0];
				st.names.add(field.getRep().toString());
				st.types.add(((PowerSetType) arg.getSecond()).getSubType());
			}
			return new PowerSetType(st);

		case OPCODE_be:
		case OPCODE_bf:
			evalBoundedExistOrForAll(n, c, expected);
			return new BooleanType();

		case OPCODE_unchanged:
			return new BooleanType();

		case 0: // no builtin
			return evalBBuiltIns(n, c, expected);

			// temporal formulas are not be translated
		case OPCODE_sa: // []_
		case OPCODE_box: // []
		case OPCODE_diamond: // <>
		case OPCODE_wf:
			c.setTemporal(true);
			return new Untyped();

		default:
			throw new NotImplementedException("No Typecheck: "
					+ n.getOperator().getName());
		}
	}

	private MyType evalElementof(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		compareTypes(n, n.getOperator().getName().toString(), expected,
				new BooleanType());
		MyType S = visitExprOrOpArgNode(n.getArgs()[1], c, new PowerSetType(
				new Untyped()));
		MyType element = visitExprOrOpArgNode(n.getArgs()[0], c,
				((PowerSetType) S).getSubType());
		visitExprOrOpArgNode(n.getArgs()[1], c, new PowerSetType(element));
		return new BooleanType();

	}

	private MyType evalSubsetOf(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		MyType res = new PowerSetType(bounded(n, c));
		compareTypes(n, "", expected, res);
		visitExprOrOpArgNode(n.getArgs()[0], c, new BooleanType());
		return res;
	}

	private MyType evalSubset(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		compareTypes(n, n.getOperator().getName().toString(), expected,
				new BooleanType());
		MyType t1 = visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(
				new Untyped()));
		MyType t2 = visitExprOrOpArgNode(n.getArgs()[1], c, t1);
		visitExprOrOpArgNode(n.getArgs()[0], c, t2);
		return new BooleanType();
	}

	private MyType bounded(OpApplNode n, DefContext c) throws MyException {
		FormalParamNode[][] nodes = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		ArrayList<MyType> list = new ArrayList<MyType>();
		for (int i = 0; i < nodes.length; i++) {
			if (n.isBdedQuantATuple()[i]) {
				ArrayList<MyType> help = new ArrayList<MyType>();
				MyType set = visitExprNode(in[i], c, new PowerSetType(
						new PairType()));
				PairType pair = (PairType) ((PowerSetType) set).getSubType();
				for (int j = 0; j < nodes[i].length; j++) {
					MyType arg = pair.getList().get(j);
					String name = nodes[i][j].getName().toString();
					// c.parameters.put(name, new Variable(name, arg));
					c.temp.put(name, new Parameter(arg));
					help.add(arg);
				}
				list.add(makePair(help));
			} else {
				MyType arg = visitExprNode(in[i], c, new PowerSetType(
						new Untyped()));
				MyType subtype = ((PowerSetType) arg).getSubType();
				for (int j = 0; j < nodes[i].length; j++) {
					String name = nodes[i][j].getName().toString();
					// c.parameters.put(name, new Variable(name, subtype));
					c.temp.put(name, new Parameter(subtype));
					list.add(subtype);
				}
			}
		}
		return makePair(list);
	}

	private void evalBoundedExistOrForAll(OpApplNode n, DefContext c,
			MyType expected) throws MyException {
		compareTypes(n, n.getOperator().getName().toString(), expected,
				new BooleanType());
		bounded(n, c);
		visitExprOrOpArgNode(n.getArgs()[0], c, new BooleanType());
	}

	private MyType evalRcdSelect(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		MyType f = visitExprOrOpArgNode(n.getArgs()[0], c, new Untyped());

		if (f.getType() != UNTYPED) {
			StructType s;
			try {
				s = (StructType) f;
			} catch (ClassCastException e) {
				throw new TypeErrorException("Expected struct(_A), but found"
						+ f + "\n" + n.getLocation());
			}
			StringNode sn;
			try {
				sn = (StringNode) n.getArgs()[1];
			} catch (Exception e) {
				throw new TypeErrorException("Expected Identifier\n"
						+ n.getLocation());
			}
			int i = s.names.indexOf(sn.getRep().toString());
			if (i == -1) {
				throw new TypeErrorException("Identifier "
						+ sn.getRep().toString() + " is invalid for " + s
						+ "\n" + n.getLocation());
			} else {
				compareTypes(n, "", expected, s.types.get(i));
				return s.types.get(i);
			}
		} else
			return new Untyped();
	}

	private MyType evalFunctionApply(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		// mehrere Argumente tuple TODO
		MyType dom = visitExprOrOpArgNode(n.getArgs()[1], c, new Untyped());
		MyType func = new PowerSetType(new PairType(dom, expected));

		MyType f = visitExprOrOpArgNode(n.getArgs()[0], c, func);
		if (f.getType() == UNTYPED) {
			return expected;
		}
		PairType pair = (PairType) ((PowerSetType) f).getSubType();
		dom = pair.getFirst();
		visitExprOrOpArgNode(n.getArgs()[1], c, dom);
		MyType range = pair.getSecond();
		return range;
	}

	private MyType evalSetOfFunction(OpApplNode n, DefContext c, MyType expected)
			throws MyException {

		MyType e = new PowerSetType(new PowerSetType(new PairType()))
				.compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected: " + expected
					+ ", found POW(POW(PAIR(_A,_B)))\n" + n.getLocation());
		}
		PairType pair = (PairType) ((PowerSetType) ((PowerSetType) e)
				.getSubType()).getSubType();
		MyType gamma1 = pair.getFirst();
		MyType gamma2 = pair.getSecond();

		MyType res1 = visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(
				gamma1));
		res1 = ((PowerSetType) res1).getSubType();

		MyType res2 = visitExprOrOpArgNode(n.getArgs()[1], c, new PowerSetType(
				gamma2));
		res2 = ((PowerSetType) res2).getSubType();
		MyType result = new PowerSetType(new PowerSetType(new PairType(res1,
				res2)));
		return result;
	}

	private MyType evalTuple(OpApplNode n, DefContext c, MyType expected)
			throws MyException {

		// Tuple as Function 1..n to Set (only one Datatype)
		ExprOrOpArgNode[] args = n.getArgs();
		MyType e = new PowerSetType(new PairType(new IntType(), new Untyped()))
				.compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected " + expected
					+ ", found Set: " + n.getLocation());
		}

		MyType t = ((PairType) ((PowerSetType) e).getSubType()).getSecond();
		int end = args.length;
		for (int i = 0; i < args.length; i++) {
			if (t.isUntyped() == false)
				end = i;
			t = visitExprOrOpArgNode(args[i], c, t);
		}
		for (int i = 0; i < end; i++) {
			visitExprOrOpArgNode(args[i], c, t);
		}
		return new PowerSetType(new PairType(new IntType(), t));

		// MyType e = new PairType().compare(expected);
		// if (e == null) {
		// throw new TypeErrorException("Expected:" + expected
		// + ", found (_A*_B) \n" + n.getLocation());
		// }
		// PairType pair = (PairType) e;
		//
		// ArrayList<MyType> l = pair.getList();
		// ArrayList<MyType> l2 = new ArrayList<MyType>();
		//
		// for (int i = 0; i < n.getArgs().length; i++) {
		// MyType res;
		// res = visitExprOrOpArgNode(n.getArgs()[i], c, l.get(i));
		// l2.add(res);
		// }
		//
		// return makePair(l2);
	}

	private MyType evalPair(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		// val:Data oder ![2] = 2
		MyType e = new PairType().compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected:" + expected
					+ ", found (_A*_B) \n" + n.getLocation());
		}
		PairType p = (PairType) e;
		MyType first = p.getFirst();
		MyType second = p.getSecond();

		MyType f = visitExprOrOpArgNode(n.getArgs()[0], c, first);
		MyType s = visitExprOrOpArgNode(n.getArgs()[1], c, second);
		return new PairType(f, s);
	}

	private MyType evalLambdaFc(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		MyType e = new PowerSetType(new PairType()).compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected " + expected
					+ ", found POW(_A*_B)" + n.getLocation());
		}
		PairType pair = (PairType) ((PowerSetType) e).getSubType();
		MyType dom = bounded(n, c);
		MyType range = visitExprOrOpArgNode(n.getArgs()[0], c, pair.getSecond());

		MyType res = new PowerSetType(new PairType(dom, range));
		compareTypes(n, "", expected, res);
		return res;
	}

	public static MyType makePair(ArrayList<MyType> list) {
		if (list.size() == 0)
			return new Untyped();
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

	private MyType evalExcept(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		MyType t = visitExprOrOpArgNode(n.getArgs()[0], c, new Untyped());
		// struct
		if (t.getType() == STRUCT) {
			return evalExceptStruct(t, n, c, expected);
		}

		MyType s;
		try {
			s = ((PowerSetType) t).getSubType();
		} catch (Exception e) {
			s = null;
		}
		if (s == null) { // searching for a Type in the replacestatements of the
			// except construct
			// ![1,2,<<TRUE,TRUE>>]= 2 , ![1] = 2
			for (int i = 1; i < n.getArgs().length; i++) {
				MyType arg = visitExprOrOpArgNode(n.getArgs()[i], c,
						new Untyped());
				if (arg.getType() != UNTYPED) {
					s = arg; // Types like (Undefined * INT), search continue
				}
				if (!arg.isUntyped()) {
					s = arg;
					break;
				}
			}
		}
		if (s == null) {
			return new Untyped();
		} else {
			for (int i = 1; i < n.getArgs().length; i++) {
				visitExprOrOpArgNode(n.getArgs()[i], c, s);
			}
			if (t.isUntyped()) {
				visitExprOrOpArgNode(n.getArgs()[0], c, new PowerSetType(s));
			}
			return new PowerSetType(s);
		}

	}

	private MyType evalExceptStruct(MyType t, OpApplNode n, DefContext c,
			MyType expected) throws MyException {
		// [chan EXCEPT !.ack = 1 - @]
		StructType st = (StructType) t;

		for (int i = 1; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];
			OpApplNode seq = (OpApplNode) pair.getArgs()[0];
			StringNode sn = (StringNode) seq.getArgs()[0];
			String name = sn.getRep().toString();
			if (!st.names.contains(name)) {
				throw new TypeErrorException(st
						+ " does not contain identifier '" + name + "'\n"
						+ sn.getLocation());
			}
			MyType temp = st.types.get(st.names.indexOf(name));
			visitExprOrOpArgNode(pair.getArgs()[1], c, temp);
		}
		return st;

	}

	private void evalOpEquals(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		compareTypes(n, n.getOperator().getName().toString(), expected,
				new BooleanType());
		MyType t1 = visitExprOrOpArgNode(n.getArgs()[0], c, new Untyped());
		MyType t2 = visitExprOrOpArgNode(n.getArgs()[1], c, t1);
		visitExprOrOpArgNode(n.getArgs()[0], c, t2);
	}

	private MyType evalSetOperator(OpApplNode n, DefContext c, MyType expected)
			throws MyException {

		MyType e = new PowerSetType(new Untyped()).compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected " + expected
					+ ", found Set: " + n.getLocation());
		}
		MyType t1 = visitExprOrOpArgNode(n.getArgs()[0], c, e);
		MyType t2 = visitExprOrOpArgNode(n.getArgs()[1], c, t1);
		visitExprOrOpArgNode(n.getArgs()[0], c, t2);
		return t2;
	}

	private MyType evalSet(OpApplNode n, DefContext c, MyType expected)
			throws MyException {
		ExprOrOpArgNode[] args = n.getArgs();
		MyType e = new PowerSetType(new Untyped()).compare(expected);
		if (e == null) {
			throw new TypeErrorException("Expected " + expected
					+ ", found Set: " + n.getLocation());
		}

		MyType t = ((PowerSetType) e).getSubType();
		int end = args.length;
		for (int i = 0; i < args.length; i++) {
			if (t.isUntyped() == false)
				end = i;
			t = visitExprOrOpArgNode(args[i], c, t);
		}
		for (int i = 0; i < end; i++) {
			visitExprOrOpArgNode(args[i], c, t);
		}
		return new PowerSetType(t);
	}

	private void evalOpMoreArgs(OpApplNode n, MyType expected, MyType found,
			MyType childType, DefContext c) throws MyException {
		compareTypes(n, n.getOperator().getName().toString(), expected, found);
		ExprOrOpArgNode[] args = n.getArgs();
		for (int i = 0; i < args.length; i++) {
			visitExprOrOpArgNode(args[i], c, childType);
		}
	}

	private MyType visitExprOrOpArgNode(ExprOrOpArgNode n, DefContext c,
			MyType expected) throws MyException {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, c, expected);
		} else if (n == null) {
			return null;
		} else {
			throw new NotImplementedException("OpArgNode not implemented jet");
		}
	}

	private void compareTypes(SemanticNode n, String name, MyType expected,
			MyType found) throws MyException {

		if (expected != null) {
			if (!expected.equals(found)) {
				String s = "Expected " + expected + ", but was " + found;
				if (!name.equals("")) {
					s += " in '" + name + "'";
				}
				s += "\n " + n.getLocation().toString();
				throw new TypeErrorException(s);
			}
		}
	}

}
