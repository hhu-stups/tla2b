package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import types.BooleanType;
import types.IType;
import types.MyType;
import types.StructType;
import types.Untyped;
import util.UniqueString;

// translator
public class Translator extends BuiltInOPs implements ASTConstants, IType,
		BBuildIns, Priorities {
	ModuleContext moduleContext;

	// ModuleNode
	public StringBuilder visitModule(ModuleNode n, ModuleContext mc) {
		moduleContext = mc;

		StringBuilder out = new StringBuilder();
		out.append("MACHINE " + n.getName().toString() + "\n");

		// Sets
		out.append(evalSets(mc));

		// Constants and Properties
		out.append(evalConsDecl(mc.constantDecl));
		out.append(evalProperties(mc, n));

		// Variables
		out.append(evalVariables(n.getVariableDecls(), mc));

		// Definitions
		out.append(evalDefinitions(n.getOpDefs(), mc));

		// INVARIANT
		out.append(evalInvarianten(mc.getInvariants(), mc));

		// Initialisierung
		out.append(evalInit(mc, n));

		// Operations
		out.append(calcOperations2(mc));

		out.append("END");
		return out;
	}

	private StringBuilder evalConsDecl(ArrayList<String> constantDecl) {
		StringBuilder out = new StringBuilder();
		if (constantDecl.size() == 0)
			return out;
		out.append("CONSTANTS ");
		for (int i = 0; i < constantDecl.size(); i++) {
			out.append(constantDecl.get(i));
			if (i < constantDecl.size() - 1) {
				out.append(", ");
			}
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalSets(ModuleContext mc) {
		StringBuilder out = new StringBuilder();
		ArrayList<String> l = mc.setEnumeration;
		if (l.size() == 0)
			return out;
		out.append("SETS\n ");
		out.append("Enum = {");
		for (int i = 0; i < l.size(); i++) {
			out.append(l.get(i));
			if (i < l.size() - 1) {
				out.append(",");
			}
		}
		out.append("}\n");
		return out;
	}

	private StringBuilder evalProperties(ModuleContext mc, ModuleNode n) {
		StringBuilder out = new StringBuilder();
		Hashtable<String, Constant> h = mc.getConstants();
		if (h.size() == 0 && n.getAssumptions().length == 0)
			return out;
		out.append("PROPERTIES\n ");
		Constant con;
		String name;

		for (int j = 0; j < mc.constantDecl.size(); j++) {
			name = mc.constantDecl.get(j);
			con = h.get(name);

			if (j != 0)
				out.append(" & ");

			if (con.getValue().equals("")) {
				out.append(con.getName() + " : " + con.getType() + "\n");
			} else {
				out.append(con.getName() + " = " + con.getValue() + "\n");
			}

		}

		if (n.getAssumptions().length > 0 && mc.constantDecl.size() > 0)
			out.append(" & ");
		// Assumptions
		out.append(evalAssumptions(n.getAssumptions(), mc));
		return out;
	}

	private StringBuilder calcOperations2(ModuleContext mc) {
		StringBuilder out = new StringBuilder();
		// Operations
		if (mc.actions.size() == 0) // no operations
			return out;
		out.append("OPERATIONS\n");

		for (int i = 0; i < mc.actions.size(); i++) {
			Action a = mc.actions.get(i);
			String name = a.name;

			DefContext d = a.defCon;
			if (((OpApplNode) ((ExprNode) mc.actions.get(i).node))
					.getOperator().getKind() == UserDefinedOpKind) {
				name = ((OpApplNode) ((ExprNode) mc.actions.get(i).node))
						.getOperator().getName().toString();
				//d = mc.definitions.get(name);
				
				//for (int j = 0; j < a.params.size(); j++) {
				//	d.temp.put(a.params.get(j), new Parameter(new Untyped()));
				//}
				
				
			}
			d = mc.definitions.get(mc.getNext());
			

			out.append(" " + name + "Op");

			// Parameters
			if (a.params.size() > 0) {
				out.append("(");
				for (int j = 0; j < a.params.size(); j++) {
					out.append(a.params.get(j));
					if (j < a.params.size() - 1) {
						out.append(", ");
					}
				}
				out.append(")");
			}

			out.append(" = ");
			out.append("ANY ");
			for (Enumeration<String> e = mc.variables.keys(); e
					.hasMoreElements();) {
				out.append(e.nextElement() + "_n");
				if (e.hasMoreElements())
					out.append(", ");
			}

			out.append("\n\tWHERE ");

			if (a.params.size() > 0) {
				out.append(visitBounded(a.parent, null));
				out.append(" & ");
			}
			
			out.append(visitExprOrOpArgNode(a.node, d, true).out);

			out.append("\n\tTHEN ");
			for (Enumeration<String> e = mc.variables.keys(); e
					.hasMoreElements();) {
				out.append(e.nextElement());
				if (e.hasMoreElements())
					out.append(", ");
			}
			out.append(" := ");
			for (Enumeration<String> e = mc.variables.keys(); e
					.hasMoreElements();) {
				out.append(e.nextElement() + "_n");
				if (e.hasMoreElements())
					out.append(", ");
			}
			out.append(" END");
			if (i != mc.actions.size() - 1) {
				out.append(";\n\n");
			}
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalInit(ModuleContext mc, ModuleNode n) {
		StringBuilder out = new StringBuilder();
		
		if (mc.variables.size() == 0 || mc.getInit().equals(""))
			return out;

		out.append("INITIALISATION\n ");

		for (int i = 0; i < n.getVariableDecls().length; i++) {

			out.append(n.getVariableDecls()[i].getName());
			if (i < n.getVariableDecls().length - 1) {
				out.append(", ");
			}
		}

		out.append(":(" + mc.getInit() + ")\n");
		return out;
	}

	private StringBuilder evalInvarianten(ArrayList<String> invs,
			ModuleContext mc) {
		StringBuilder out = new StringBuilder();
		if (mc.variables.size() > 0) {
			out.append("INVARIANT\n ");
			for (int i = 0; i < invs.size(); i++) {
				out.append(invs.get(i));
				if (i != invs.size() - 1)
					out.append(" & ");
			}
			out.append("");
		}
		if (mc.getInvariants().size() > 0) {
			out.append(" & ");
		}
		int counter = 0;
		Enumeration<Variable> e = mc.variables.elements();
		while (e.hasMoreElements()) {
			Variable v = e.nextElement();

			out.append(v.getName() + " :" + v.getType() + "");
			if (counter < mc.variables.size() - 1) {
				out.append(" & ");
			}
			counter++;
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalDefinitions(OpDefNode[] opDefs, ModuleContext mc) {
		ArrayList<String> standardModules = new ArrayList<String>();
		standardModules.add("TLC");
		standardModules.add("Naturals");
		standardModules.add("Integers");
		standardModules.add("FiniteSets");
		standardModules.add("Sequences");
		StringBuilder out = new StringBuilder();
		if (opDefs.length == 0)
			return out;

		if (opDefs.length > 0
				&& opDefs[opDefs.length - 1].getOriginallyDefinedInModuleNode()
						.equals(mc.getRoot()))
			out.append("DEFINITIONS\n");

		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
			DefContext dc;
			/*
			 * if (def.getName().equals("Spec")) continue; else
			 */
			if (def.getName().toString().equals(mc.getNext())
					&& def.getOriginallyDefinedInModuleNode().equals(
							mc.getRoot())) {
				evalNext(def, mc);
				dc = mc.definitions.get(def.getName().toString());
				dc.setNext(true);
				out.append(visitOpDefNode(def, dc));
			}

			// Definition in this module
			else if (!standardModules.contains(def
					.getOriginallyDefinedInModuleNode().getName().toString())) {
				dc = mc.definitions.get(def.getName().toString());
				if (!dc.isTemporal()) {
					out.append(visitOpDefNode(def, dc));
				}
			}

		}

		// for (int i = 0; i < mc.lets.size(); i++) {
		// DefContext dd = mc.definitions.get(mc.lets.get(i).getName()
		// .toString());
		// out.append(visitOpDefNode(mc.lets.get(i), dd));
		// }

		return out;

	}

	private void evalNext(OpDefNode n, ModuleContext mc) {
		getActions(n.getBody(), n.getName().toString(), mc, null);
	}

	private void getActions(SemanticNode next, String name, ModuleContext c,
			OpApplNode params) {
		switch (next.getKind()) {
		case OpApplKind: {
			OpApplNode next1 = (OpApplNode) next;
			this.getActionsAppl(next1, name, c, params);
			return;
		}
		case LetInKind: {
			//TODO
			LetInNode next1 = (LetInNode) next;
			this.getActions(next1.getBody(), name, c, params);
			return;
		}
		case SubstInKind:
		case LabelKind:
		default:
			System.err.println("Next typ noch unbekannt");
		}

	}

	private void getActionsAppl(OpApplNode node, String name, ModuleContext c,
			OpApplNode params) {
		int opcode = getOpCode(node.getOperator().getName());
		switch (opcode) {
		case OPCODE_be: // BoundedExists
		{
			
			if (params == null) {
				this.getActions(node.getArgs()[0], name, c, node);
			} else {
				Action a = new Action(name, node);
				//a.defCon = c.definitions.get(name);
				//this.getActions(node.getArgs()[0], name, c, params);
				a.boundedExists(params);
				c.actions.add(a);
			}
			return;
		}

		case OPCODE_dl: // DisjList
		case OPCODE_lor: {
			for (int i = 0; i < node.getArgs().length; i++) {
				this.getActions(node.getArgs()[i], name+ (i + 1), c, params);
			}
			return;
		}
		default: {
			// We handle all the other builtin operators here.
			Action a = new Action(name, node);
			a.boundedExists(params);
			//a.defCon = c.definitions.get(c.getNext());
			c.actions.add(a);
			return;
		}
		}
	}

	private StringBuilder evalVariables(OpDeclNode[] vars, ModuleContext mc) {
		StringBuilder out = new StringBuilder();
		if (vars.length > 0) {
			out.append("VARIABLES ");
			for (int i = 0; i < vars.length; i++) {
				String name = visitOpDeclNode(vars[i]);
				out.append(name);
				if (i != vars.length - 1)
					out.append(", ");
			}
			out.append("\n");
		}
		return out;
	}

	private StringBuilder evalAssumptions(AssumeNode[] assumptions,
			ModuleContext mc) {
		StringBuilder out = new StringBuilder();
		boolean notFirst = false;
		for (AssumeNode assumeNode : assumptions) {
			if (notFirst) {
				out.append(" & ");
			}
			out.append(visitAssumeNode(assumeNode, mc));
			out.append("\n");
			notFirst = true;
		}
		return out;
	}

	public StringBuilder visitAssumeNode(AssumeNode n, ModuleContext mc) {
		// there are named or unnamend assumptions
		StringBuilder out = new StringBuilder();

		// named
		/*
		 * if(n.getDef()!= null){ visitThmOrAssumpDefNode(n.getDef(), mc); }
		 */
		DefContext defCon = (DefContext)n.getToolObject(1);
		out.append(visitExprNode(n.getAssume(), defCon, true).out);

		return out;
	}

	// Variablen und Konstanten
	public String visitOpDeclNode(OpDeclNode n) {
		return n.getName().toString();
	}

	// Definitions
	public StringBuilder visitOpDefNode(OpDefNode n, DefContext dc) {
		StringBuilder out = new StringBuilder();
		out.append(" " + n.getName());
		String[] ps = dc.getParams();
		if (ps.length > 0) {
			out.append("(");
			for (int i = 0; i < ps.length; i++) {
				out.append(ps[i]);
				if (i < ps.length - 1) {
					out.append(",");
				}
			}
			out.append(")");
		}
		out.append(" == ");
		boolean makePred = true;
		if (dc.getType().getType() == BOOLEAN) {
			BooleanType b = (BooleanType) dc.getType();
			makePred = !b.isBoolValue();
		}
		out.append(visitExprNode(n.getBody(), dc, makePred).out);
		out.append(";\n");
		return out;
	}

	public String visitFormalParamNode(FormalParamNode n) {
		return n.getName().toString();
	}

	public ExprReturn visitOpApplNode(OpApplNode n, DefContext c,
			boolean makePred) {
		StringBuilder out = new StringBuilder();
		int priority = P_max;
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind:
			out.append(visitOpDeclNode((OpDeclNode) n.getOperator()));
			return new ExprReturn(out, priority);

		case VariableDeclKind:
			String name2 = n.getOperator().getName().toString();
			out.append(name2);
			if (makePred
					&& moduleContext.variables.get(name2).getType().getType() == BOOLEAN) {
				out.append(" = TRUE");
			}
			return new ExprReturn(out, priority);

		case UserDefinedOpKind: {
			String name = n.getOperator().getName().toString();

			// Operator ist ein B-BuiltIn-Operator
			if (BBuiltInOPs.contains(n.getOperator().getName())) {
				return evalBBuiltIns(n, c, makePred);
			}

			// Definition ist eine Subdefinition
			if (c.lets.containsKey(name)) {
				OpDefNode node = c.lets.get(name).getNode();

				DefContext defCon = c.lets.get(name).getDefCon();


				for (int i = 0; i < defCon.getParams().length; i++) {
					String pname = defCon.getParams()[i];
					defCon.parameters.get(pname).setEr(
							visitExprOrOpArgNode(n.getArgs()[i], c, false));
				}
				return visitExprNode(node.getBody(), defCon, makePred);
			}

			out.append(name);
			if (n.getArgs().length > 0) {
				out.append("(");
				for (ExprOrOpArgNode arg : n.getArgs()) {
					out.append(visitExprOrOpArgNode(arg, c, false).out);
					out.append(", ");
				}
				out.delete(out.length() - 2, out.length());
				out.append(")");

			}
			MyType t = moduleContext.definitions.get(name).getType();
			if (t.getType() == BOOLEAN) {
				BooleanType b = (BooleanType) t;
				if (!b.isBoolValue()) {
					return new ExprReturn(makeBoolExpression(!makePred, out),
							priority);
				} else if (b.isBoolValue() && makePred) {
					out.append(" = TRUE");
				}
			}
			return new ExprReturn(out, priority);
		}

		case BuiltInKind:
			return evalBuiltInKind(n, c, makePred);

		case FormalParamKind: {
			String name = n.getOperator().getName().toString();

			// Subdefintion Parameter
			if (c.parameters.containsKey(name)) {
				Parameter p = c.parameters.get(name);
				if (p.hasValue()) {
					ExprReturn er = p.getEr();
					if (makePred && p.getType().getType() == BOOLEAN) {
						er.out.append(" = TRUE");
					}

					return er;
				}

			}
			out.append(name);
			if (c.temp.containsKey(name)) {
				Parameter b = (Parameter) n.getToolObject(0);
				// return c.temp.get(name);
				if (makePred && b.getType().getType() == BOOLEAN) {
					out.append(" = TRUE");
					return new ExprReturn(out, P_equals);
				}
			}
			if (makePred && c.parameters.get(name) != null
					&& c.parameters.get(name).getType().getType() == BOOLEAN) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out, P_max);
		}

		default:
			break;
		}

		out.append("[" + n.getOperator().getKind()
				+ " Kein bekannter OppAppl-Typ]");
		return new ExprReturn(out, priority);

	}

	private ExprReturn evalBBuiltIns(OpApplNode n, DefContext c,
			boolean makePred) {
		// B Builtins
		UniqueString name = n.getOperator().getName();
		StringBuilder out = new StringBuilder();
		int priority = P_max;

		switch (BBuiltInOPs.getOpcode(name)) {
		
		/************* Module Naturals ***************/
		case B_OPCODE_dotdot: // ..
			out.append(evalOp2Args(n, "..", c, false, P_dotdot));
			return new ExprReturn(out, P_dotdot);

		case B_OPCODE_gt: // >
			out.append(evalOp2Args(n, " > ", c, false, P_gt));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_gt);

		case B_OPCODE_lt: // <
			out.append(evalOp2Args(n, " < ", c, false, P_lt));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_lt);

		case B_OPCODE_leq: // <=
			out.append(evalOp2Args(n, " <= ", c, false, P_leq));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_leq);

		case B_OPCODE_geq: // >=
			out.append(evalOp2Args(n, " >= ", c, false, P_geq));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_geq);

		case B_OPCODE_plus: // +
			out.append(evalOp2Args(n, " + ", c, false, P_plus));
			return new ExprReturn(out, P_plus);

		case B_OPCODE_minus: // -
			out.append(evalOp2Args(n, " - ", c, false, P_minus));
			return new ExprReturn(out, P_minus);

		case B_OPCODE_times: // *
			out.append(evalOp2Args(n, " * ", c, false, P_times));
			return new ExprReturn(out, P_times);

		case B_OPCODE_div: // /
			out.append(evalOp2Args(n, " / ", c, false, P_div));
			return new ExprReturn(out, P_div);

		case B_OPCODE_mod: // modulo
			out.append(evalOp2Args(n, " mod ", c, false, P_mod));
			return new ExprReturn(out, P_mod);
			
		case B_OPCODE_exp: // x hoch y, x^y
			out.append(evalOp2Args(n, " ** ", c, false, P_exp));
			return new ExprReturn(out, P_exp);

		case B_OPCODE_nat: // Nat
			out.append("NATURAL");
			return new ExprReturn(out, priority);
			
			
		/************* Module Integers ***********************/	
		case B_OPCODE_int: // Int
			out.append("INTEGER");
			return new ExprReturn(out, priority);
			
		case B_OPCODE_uminus: // unary minus
			out.append("-");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			return new ExprReturn(out, P_uminus);

		/************** Standard Module FiniteSets ********************/
		case B_OPCODE_card: // Cardinality
			out.append("card(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out, priority);
			
		case B_OPCODE_finite: // IsFiniteSet TODO
		{
			out.append("!f_.(f_ : ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(" => #f2_.(f2_ : ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append("f2_>f_)))");
			return new ExprReturn(makeBoolExpression(!makePred, out), priority); 
		}

		/************* Standard Module Sequences  **************************/
		case B_OPCODE_len: // length of the sequence
			out.append("size(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out);
			
		case B_OPCODE_append: // Append(s,x)
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append("<-");
			out.append(visitExprOrOpArgNode(n.getArgs()[1], c, false).out);
			return new ExprReturn(out, P_append);
			
		case B_OPCODE_head: //Head(s)
			out.append("first(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out);
			
		case B_OPCODE_tail: //Tail(s)
			out.append("tail(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out);
			
		case B_OPCODE_conc: // s \o s2 - concatenation of s and s2
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append("^");
			out.append(visitExprOrOpArgNode(n.getArgs()[1], c, false).out);
			return new ExprReturn(out, P_conc);
			
		case B_OPCODE_subseq: // SubSeq(s,m,n)
		{
			StringBuilder s = visitExprOrOpArgNode(n.getArgs()[0], c, false).out;
			out.append("(");
			out.append(s);
			out.append("\\|/"); // drop first elements
			out.append(visitExprOrOpArgNode(n.getArgs()[1], c, false).out);
			out.append("-1)");
			out.append("/|\\");
			out.append(visitExprOrOpArgNode(n.getArgs()[2], c, false).out);
			out.append("-");
			out.append(brackets(visitExprOrOpArgNode(n.getArgs()[1], c, false), P_minus, false));
			out.append("+1");
			return new ExprReturn(out, P_take_first);
		}
		
		case B_OPCODE_seq: //Set of Sequences
		{
			out.append("seq(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out);
		}
			
		
			// TLA Builtins, but not in tool.BuiltInOPs
		case B_OPCODE_bool: // BOOLEAN
			out.append("BOOL");
			return new ExprReturn(out, priority);

		case B_OPCODE_true: // TRUE
			out.append("TRUE");
			if (makePred)
				out.append(" = TRUE");
			return new ExprReturn(out, priority);

		case B_OPCODE_false: // FALSE
			out.append("FALSE");
			if (makePred)
				out.append(" = TRUE");
			return new ExprReturn(out, priority);

		case B_OPCODE_string: // STRING
			out.append("STRING");
			return new ExprReturn(out, priority);
		
		default:
			System.err.println("unknown B Builtin: "
					+ n.getOperator().getName());
			out.append(n.getOperator().getName() + "??");
			return new ExprReturn(out, priority);
		}

	}

	private StringBuilder brackets(ExprReturn r, int p, boolean left) {
		StringBuilder res = new StringBuilder();
		if ((left && r.getPriority() < p) || (!left && r.getPriority() <= p)) {
			res.append("(");
			res.append(r.getOut());
			res.append(")");
		} else
			res.append(r.getOut());
		return res;
	}

	private ExprReturn evalBuiltInKind(OpApplNode n, DefContext c,
			boolean makePred) {
		StringBuilder out = new StringBuilder();
		int priority = P_max;
		ExprReturn res = new ExprReturn();
		switch (getOpCode(n.getOperator().getName())) {

		case OPCODE_cl: // $ConjList
		case OPCODE_land: // \land
			out.append(evalOpMoreArgs(n, " & ", c, true, P_and));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_and);

		case OPCODE_dl: // $DisjList
		case OPCODE_lor: // \/
			out.append(evalOpMoreArgs(n, " or ", c, true, P_or));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_or);

		case OPCODE_equiv: // \equiv
			out.append(evalOp2Args(n, " <=> ", c, true, P_equiv));
			return new ExprReturn(out, P_equiv);

		case OPCODE_implies: // =>
			out.append("(");
			out.append(evalOp2Args(n, " => ", c, true, P_implies));
			out.append(")");
			return new ExprReturn(out, P_implies);

		case OPCODE_uc: { // CHOOSE x : P
			out.append("({TRUE}*{");
			out.append(n.getUnbdedQuantSymbols()[0].getName());
			out.append("|");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, true).out);
			out.append("})(TRUE)");
			return new ExprReturn(out, P_max);
		}

		case OPCODE_bc: { // CHOOSE x \in S : P
			out.append("({TRUE}*");
			out.append(evalSubsetOf(n, c).out);
			out.append(")(TRUE)");
			return new ExprReturn(out, P_max);
		}

		case OPCODE_noteq: // /=
			out.append(evalOp2Args(n, " /= ", c, false, P_noteq));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_noteq);

		case OPCODE_eq: // =
			out.append(evalOp2Args(n, " = ", c, false, P_equals));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_equals);

		case OPCODE_lnot: // \lnot
			out.append(" not(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, true).out);
			out.append(")");
			return new ExprReturn(makeBoolExpression(!makePred, out), P_max);

		case OPCODE_in: // \in
			out.append(evalOp2Args(n, " : ", c, false, P_in));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_in);

		case OPCODE_notin: // \notin
			out.append(evalOp2Args(n, " /: ", c, false, P_notin));
			return new ExprReturn(makeBoolExpression(!makePred, out), P_notin);

			// Quantoren
		case OPCODE_be: // $BoundedExists Represents \E x \in S : P.
			out.append(evalQuantor(n, c, makePred, "#"));
			return new ExprReturn(out, priority);

		case OPCODE_bf: // \$BoundedForall Represents \A x \in S : P.
			out.append(evalQuantor(n, c, makePred, "!"));
			return new ExprReturn(out, priority);

			// temporal
		case OPCODE_sa: // $SquareAct
			c.setTemporal(true);
			out.append("[");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, makePred).out);
			out.append("]_");
			out.append(visitExprOrOpArgNode(n.getArgs()[1], c, makePred).out);
			return new ExprReturn(out, priority);

		case OPCODE_box: // []
			c.setTemporal(true);
			out.append("[]");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, makePred).out);
			return new ExprReturn(out, priority);

		case OPCODE_cp: // $CartesianProd A \X B \X C as $CartesianProd(A, B, C)
			out.append(evalOpMoreArgs(n, "*", c, false, P_times));
			return new ExprReturn(out, P_times);

		case OPCODE_tup: // $Tuple << >>
			out.append("[");
			out.append(evalOpMoreArgs(n, ", ", c, false, P_min));
			out.append("]");
			return new ExprReturn(out, P_max);
//			out.append("(");
//			out.append(evalOpMoreArgs(n, "|-> ", c, false, P_maplet));
//			out.append(")");
//			return new ExprReturn(out, P_maplet);

		case OPCODE_prime: // prime
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, makePred).out);
			out.append("_n");
			res.out = out;
			return res;

			// Mengen
		case OPCODE_subset: // SUBSET
			out.append("POW(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out, priority);

		case OPCODE_union: // Union
			out.append("union(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out, priority);

		case OPCODE_se: // SetEnumeration {1,2,3}
			out.append("{");
			out.append(evalOpMoreArgs(n, ", ", c, false, P_comma));
			out.append("}");
			return new ExprReturn(out, P_max);

		case OPCODE_sso: // $SubsetOf Represents {x \in S : p}.
			return evalSubsetOf(n, c);
		case OPCODE_soa: // $SetOfAll Represents {e : x \in S}.
			return evalSetOfAll(n, c);

		case OPCODE_cup: // \/
			out.append(evalOp2Args(n, " \\/ ", c, false, P_union));
			return new ExprReturn(out, P_union);

		case OPCODE_cap: // \intersect /\
			out.append(evalOp2Args(n, " /\\ ", c, false, P_intersect));
			return new ExprReturn(out, P_intersect);

		case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
			out.append(evalOp2Args(n, " <: ", c, false, P_subseteq));
			return new ExprReturn(out, P_subseteq);

		case OPCODE_setdiff: // Setdifferenz T - U
			out.append(evalOp2Args(n, " - ", c, false, P_setdiff));
			return new ExprReturn(out, P_setdiff);

			// Konstrukte
		case OPCODE_ite: // IF THEN ELSE
			return evalIfThenElse(n, c, makePred);

		case OPCODE_case: // CASE p1 -> e1 [] p2 -> e2
		{
			out.append("(");
			StringBuilder all = new StringBuilder();
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];

				out.append("%t_.(");
				if (pair.getArgs()[0] == null) {
					out.append("not(" + all + ")");
				} else {
					ExprReturn p = visitExprOrOpArgNode(pair.getArgs()[0], c,
							true);
					if (i != 0) {
						all.append(" or ");
					}
					all.append(brackets(p, P_or, false));
					out.append(p.out);
				}

				out.append(" | ");
				out
						.append(visitExprOrOpArgNode(pair.getArgs()[1], c,
								false).out);
				out.append(")");
				if (i < n.getArgs().length - 1) {
					out.append(" \\/ ");
				}
			}

			out.append(")(TRUE)");

			if (makePred) {
				out.append(" = TRUE");
			}
			return new ExprReturn(out, P_max);
		}

		/************** Functions ******************/

		case OPCODE_nrfs:
		case OPCODE_fc: // Represents [x \in S |-> e].
			out.append("%");
			FormalParamNode[][] vars = n.getBdedQuantSymbolLists();
			for (int i = 0; i < vars.length; i++) {
				for (int j = 0; j < vars[i].length; j++) {
					out.append(vars[i][j].getName());
					if (j < vars[i].length - 1) {
						out.append(",");
					}
				}
				if (i < vars.length - 1) {
					out.append(",");
				}
			}
			out.append(".(");
			out.append(visitBounded(n, c));
			out.append("| ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out, priority);

		case OPCODE_fa: // f[1]
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append("(");
			ExprOrOpArgNode[] args = n.getArgs();
			for (int i = 1; i < args.length; i++) {
				out.append(visitExprOrOpArgNode(args[i], c, false).out);
				if (i != args.length - 1)
					out.append(",");
			}
			out.append(")");
			return new ExprReturn(out, priority);
			
		case OPCODE_domain:
			out.append("dom(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(")");
			return new ExprReturn(out, P_max);

			// Records
		case OPCODE_sor: // x \in [val : Data, rdy : {0, 1}, ack : {0, 1}]
			return evalStructOrRec("struct", n, c);

		case OPCODE_rc: // [h_1 |-> 1, h_2 |-> 2]
		{
			return evalStructOrRec("rec", n, c);
		}

		case OPCODE_rs: // x.val
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append("'");
			StringNode stringNode = (StringNode) n.getArgs()[1];
			out.append(stringNode.getRep().toString());
			// out.append(evalOpMoreArgs(n, "'", c, false, P_record_acc));
			return new ExprReturn(out, P_record_acc);

		case OPCODE_pair: // val:Data oder ![2] = 2 //
			out.append(evalOpMoreArgs(n, " |-> ", c, false, P_maplet));
			return new ExprReturn(out, P_maplet);

		case OPCODE_sof: // SetOfFunction [T -> U]
			out.append(evalOp2Args(n, " --> ", c, false, P_total_f));
			return new ExprReturn(out, P_total_f);

		case OPCODE_exc: // Except
			return evalExcept(n, c);

		case OPCODE_seq: // !
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			return new ExprReturn(out, priority);

		case OPCODE_unchanged:
			OpApplNode k = (OpApplNode) n.getArgs()[0];
			if (k.getOperator().getKind() == VariableDeclKind) {
				String name = visitOpDeclNode((OpDeclNode) k.getOperator());
				out.append(name + "_n = " + name);
			} else {
				// Tuple
				for (int i = 0; i < k.getArgs().length; i++) {
					String name = visitExprOrOpArgNode(k.getArgs()[i], c, false).out
							.toString();
					out.append(name + "_n = " + name);
					if (i < k.getArgs().length - 1) {
						out.append("\n\t& ");
					}
				}
			}
			return new ExprReturn(out, P_max);

		case 0: // no builtin!
			return evalBBuiltIns(n, c, makePred);

		default:
			out.append(n.getOperator().getName() + "?");
			out.append(getOpCode(n.getOperator().getName()));
			return new ExprReturn(out, priority);
		}
	}

	private ExprReturn evalSetOfAll(OpApplNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		out.append("{t_|#");
		FormalParamNode[][] vars2 = n.getBdedQuantSymbolLists();
		for (int i = 0; i < vars2.length; i++) {
			for (int j = 0; j < vars2[i].length; j++) {
				out.append(vars2[i][j].getName());
				if (j < vars2[i].length - 1) {
					out.append(",");
				}
			}
			if (i < vars2.length - 1) {
				out.append(",");
			}
		}
		out.append(".(");
		out.append(visitBounded(n, c));
		out.append(" & t_ = ");
		out.append(visitExprOrOpArgNode(n.getArgs()[0], c, true).out);
		out.append(")}");
		return new ExprReturn(out);
	}

	private ExprReturn evalSubsetOf(OpApplNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		out.append("{");
		FormalParamNode[][] vars2 = n.getBdedQuantSymbolLists();
		for (int i = 0; i < vars2.length; i++) {
			for (int j = 0; j < vars2[i].length; j++) {
				out.append(vars2[i][j].getName());
				if (j < vars2[i].length - 1) {
					out.append(",");
				}
			}
			if (i < vars2.length - 1) {
				out.append(",");
			}
		}
		out.append("|");
		out.append(visitBounded(n, c));
		out.append(" & ");
		out.append(visitExprOrOpArgNode(n.getArgs()[0], c, true).out);
		out.append("}");
		return new ExprReturn(out);
	}

	private StringBuilder evalQuantor(OpApplNode n, DefContext c,
			boolean makePred, String s1) {
		String s2 = "";
		if (s1.equals("#")) {
			s2 = " & ";
		} else if (s1.equals("!")) {
			s2 = " => ";
		}
		StringBuilder out = new StringBuilder();
		out.append(s1);

		FormalParamNode[][] vars2 = n.getBdedQuantSymbolLists();
		for (int i = 0; i < vars2.length; i++) {
			for (int j = 0; j < vars2[i].length; j++) {
				out.append(vars2[i][j].getName());
				if (j < vars2[i].length - 1) {
					out.append(",");
				}
			}
			if (i < vars2.length - 1) {
				out.append(",");
			}
		}
		out.append(".(");
		out.append(visitBounded(n, c));
		out.append(s2);
		out.append(visitExprOrOpArgNode(n.getArgs()[0], c, true).out);
		out.append(")");
		return makeBoolExpression(!makePred, out);
	}

	private StringBuilder makeBoolExpression(boolean makeExpr, StringBuilder out) {
		StringBuilder res = new StringBuilder();
		if (makeExpr) {
			res.append("bool(" + out + ")");
		} else {
			res.append(out);
		}
		return res;
	}

	private ExprReturn evalExcept(OpApplNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		String name = visitExprOrOpArgNode(n.getArgs()[0], c, false).out
				.toString();
		Variable v = moduleContext.variables.get(name);
		if (v == null || v.getType().getType() != STRUCT) {
			out.append(visitExprOrOpArgNode(n.getArgs()[0], c, false).out);
			out.append(" <+ {");
			for (int i = 1; i < n.getArgs().length; i++) {
				out.append(visitExprOrOpArgNode(n.getArgs()[i], c, false).out);
				if (i < n.getArgs().length - 1) {
					out.append(", ");
				}
			}
			out.append("}");
			// out.append(evalOpMoreArgs(n, " | ", c));
			return new ExprReturn(out, 0);
		}

		Hashtable<String, String> temp = new Hashtable<String, String>();
		for (int i = 1; i < n.getArgs().length; i++) {
			// out.append(b)
			StringNode s = (StringNode) n.getArgs()[i].getChildren()[0]
					.getChildren()[0];
			String nodeName = s.getRep().toString();
			String val = visitExprOrOpArgNode((ExprOrOpArgNode) n.getArgs()[i]
					.getChildren()[1], c, false).out.toString();
			temp.put(nodeName, val);
		}

		out.append("rec(");
		StructType st = (StructType) v.getType();
		for (int i = 0; i < st.names.size(); i++) {
			String n2 = st.names.get(i);
			out.append(n2);
			out.append(" : ");
			String value = temp.get(n2);
			if (value == null) {
				value = name + "'" + n2;
			}
			out.append(value);
			if (i < st.names.size() - 1) {
				out.append(", ");
			}
		}
		out.append(")");
		return new ExprReturn(out, 0);

	}

	private ExprReturn evalStructOrRec(String string, OpApplNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		out.append(string);
		out.append("(");
		ExprOrOpArgNode[] args = n.getArgs();
		for (int i = 0; i < args.length; i++) {
			OpApplNode pair = (OpApplNode) args[i];
			StringNode stringNode = (StringNode) pair.getArgs()[0];
			out.append(stringNode.getRep().toString());
			out.append(" : ");
			out.append(visitExprOrOpArgNode(pair.getArgs()[1], c, false).out);
			if (i != args.length - 1)
				out.append(", ");
		}
		out.append(")");
		return new ExprReturn(out, P_max);
	}

	public StringBuilder visitBounded(OpApplNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		FormalParamNode[][] nodes = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		for (int i = 0; i < nodes.length; i++) {
			if (n.isBdedQuantATuple()[i]) {
				out.append("(");
				for (int j = 0; j < nodes[i].length; j++) {
					out.append(nodes[i][j].getName());
					if (j < nodes[i].length - 1) {
						out.append("|->");
					}
				}
				out.append(") : ");
				out.append(visitExprNode(in[i], c, false).out);
			} else {
				for (int j = 0; j < nodes[i].length; j++) {
					out.append(nodes[i][j].getName());
					out.append(" : ");
					out.append(visitExprNode(in[i], c, false).out);
					if (j < nodes[i].length - 1) {
						out.append(" & ");
					}
				}
			}
			if (i < nodes.length - 1) {
				out.append(" & ");
			}
		}
		return out;
	}

	private StringBuilder evalOp2Args(OpApplNode n, String s, DefContext c,
			boolean isEquation, int priority) {
		StringBuilder out = new StringBuilder();
		ExprReturn r;
		r = visitExprOrOpArgNode(n.getArgs()[0], c, isEquation);
		out.append(brackets(r, priority, true));
		out.append(s);
		r = visitExprOrOpArgNode(n.getArgs()[1], c, isEquation);
		out.append(brackets(r, priority, false));
		return out;
	}

	private StringBuilder evalOpMoreArgs(OpApplNode n, String s, DefContext c,
			boolean isEquation, int priority) {
		StringBuilder out = new StringBuilder();
		ExprOrOpArgNode[] args = n.getArgs();
		for (int i = 0; i < args.length; i++) {
			ExprReturn r = visitExprOrOpArgNode(args[i], c, isEquation);
			if (i == 0) {
				out.append(brackets(r, priority, true));
			} else {
				out.append(s);
				out.append(brackets(r, priority, false));
			}

		}
		return out;
	}

	private ExprReturn evalIfThenElse(OpApplNode n, DefContext c,
			boolean makePred) {
		String res;
		ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], c, true);
		ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], c, makePred);
		ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], c, makePred);
		
		MyType t = (MyType) n.getToolObject(1);
		if (!makePred || t.getType()!= BOOLEAN) {
			res = "(%t_.(" + iif.out + " | " + then.out + ")\\/%t_.(not("
					+ iif.out + ") | " + eelse.out + "))(0)";
			return new ExprReturn(res, P_max);
		} else {
			res = "(" + iif.out + " => " + then.out + ") & (not(" + iif.out
					+ ") => " + eelse.out + ")";
			return new ExprReturn(res, P_max);
		}

	}

	public ExprReturn visitExprNode(ExprNode n, DefContext c, boolean makePred) {

		switch (n.getKind()) {
		case OpApplKind:
			return visitOpApplNode((OpApplNode) n, c, makePred);

		case NumeralKind:
			return visitNumeralNode((NumeralNode) n, c);

		case StringKind: {
			StringBuilder sb = new StringBuilder();
			StringNode s = (StringNode) n;
			sb.append("\"" + s.getRep() + "\"");
			return new ExprReturn(sb);
		}

		case AtNodeKind: // @
			StringBuilder sb2 = new StringBuilder();
			AtNode a = (AtNode) n;
			String base = visitExprNode(a.getAtBase(), c, makePred).out
					.toString();
			if (moduleContext.variables.get(base).getType().getType() == STRUCT) {
				sb2.append(base + "'");
				StringNode stringnode = (StringNode)((OpApplNode) a.getAtModifier()).getArgs()[0];
				sb2.append(stringnode.getRep().toString());
				//sb2.append(visitOpApplNode(a.getAtModifier(), c, makePred).out);
			} else {
				sb2.append(base);
				sb2.append("(");
				sb2.append(visitOpApplNode(a.getAtModifier(), c, makePred).out);
				sb2.append(")");
			}
			return new ExprReturn(sb2);

		case LetInKind: // LET/IN- Konstrukt
		{
			// StringBuilder sb = new StringBuilder();
			// LetInNode l = (LetInNode) n;
			// for (int i = 0; i < l.getLets().length; i++) {
			// moduleContext.lets.add(l.getLets()[i]);
			// }
			LetInNode l = (LetInNode) n;
			// for (int i = 0; i < l.getLets().length; i++) {
			// c.lets.put(l.getLets()[i].getName().toString(), l.getLets()[i]);
			// }

			return visitExprNode(l.getBody(), c, true);
		}

		default:
			System.err.println("unbekannter Typ: " + n.getKind());
			break;
		}
		return null;
	}

	public ExprReturn visitExprOrOpArgNode(ExprOrOpArgNode n, DefContext c,
			boolean makePred) {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, c, makePred);
		} else {
			return new ExprReturn("OpArgNode not implemented jet");
		}
	}

	public ExprReturn visitNumeralNode(NumeralNode n, DefContext c) {
		StringBuilder out = new StringBuilder();
		out.append(n.val());
		return new ExprReturn(out);
	}

}
