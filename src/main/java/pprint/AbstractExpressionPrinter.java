/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package pprint;

import global.BBuildIns;
import global.BBuiltInOPs;
import global.Priorities;
import global.TranslationGlobals;

import java.util.Hashtable;

import config.TLCValueNode;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import types.BType;
import types.EnumType;
import types.IType;
import types.PowerSetType;
import types.StructType;

public abstract class AbstractExpressionPrinter extends BuiltInOPs implements
		ASTConstants, IType, BBuildIns, Priorities, TranslationGlobals {
	// private int substitutionId = 10;

	final int NOBOOL = 0;
	final int VALUE = 1;
	final int PREDICATE = 2;
	final int VALUEORPREDICATE = 3;

	protected ExprReturn visitExprOrOpArgNode(ExprOrOpArgNode n, DContext d,
			int expected) {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, d, expected);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	protected ExprReturn visitExprNode(ExprNode n, DContext d, int expected) {
		StringBuilder out = new StringBuilder();
		switch (n.getKind()) {
		case OpApplKind:
			return visitOpApplNode((OpApplNode) n, d, expected);

		case NumeralKind: {
			out.append(((NumeralNode) n).val());
			return new ExprReturn(out);
		}

		case StringKind: {
			StringNode s = (StringNode) n;
			out.append("\"" + s.getRep() + "\"");
			return new ExprReturn(out);
		}

		case LetInKind: {
			LetInNode letInNode = (LetInNode) n;
			return visitLetInNode(letInNode, d, expected);

		}
		case AtNodeKind: { // @
			AtNode at = (AtNode) n;
			String base = visitExprNode(at.getAtBase(), d, NOBOOL).out
					.toString();
			BType t = (BType) at.getExceptRef().getToolObject(TYPE_ID);
			if (t.getKind() == STRUCT) {
				out.append(base + "'");
				StringNode stringNode = (StringNode) ((OpApplNode) at
						.getAtModifier()).getArgs()[0];
				out.append(stringNode.getRep().toString());
				return new ExprReturn(out, P_record_acc);
			} else {
				// Function
				ExprOrOpArgNode domExpr = at.getAtModifier().getArgs()[0];
				out.append(base + "(");
				if (domExpr instanceof OpApplNode
						&& ((OpApplNode) domExpr).getOperator().getName()
								.toString().equals("$Tuple")) {
					OpApplNode domOpAppl = (OpApplNode) domExpr;
					for (int j = 0; j < domOpAppl.getArgs().length; j++) {
						if (j != 0) {
							out.append(", ");
						}
						out.append(visitExprOrOpArgNode(domOpAppl.getArgs()[j],
								d, VALUE).out);
					}
				} else {
					out.append(visitExprOrOpArgNode(domExpr, d, VALUE).out);
				}
				out.append(")");
				return new ExprReturn(out);
			}
		}
		case TLCValueKind: {
			TLCValueNode val = (TLCValueNode) n;
			return new ExprReturn(val.getValue().toString());
		}

		}
		throw new RuntimeException(n.toString(2));
	}

	protected ExprReturn visitLetInNode(LetInNode l, DContext d, int expected) {
		for (int i = 0; i < l.getLets().length; i++) {
			// do something
		}
		return visitExprNode(l.getBody(), d, VALUEORPREDICATE);
	}

	private ExprReturn visitOpApplNode(OpApplNode n, DContext d, int expected) {
		StringBuilder out = new StringBuilder();
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			out.append(getPrintName(n.getOperator()));
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}
		case VariableDeclKind: {
			out.append(getPrintName(n.getOperator()));
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}
		case BuiltInKind:
			return evalBuiltInKind(n, d, expected);

		case FormalParamKind: {
			return visitFormalParamNode(n, d, expected);
		}

		case UserDefinedOpKind: {
			return visitUserdefinedOp(n, d, expected);
		}

		}
		throw new RuntimeException(n.toString(2));
	}

	/**
	 * @param n
	 * @param d
	 * @param expected
	 * @return
	 */
	protected ExprReturn visitFormalParamNode(OpApplNode n, DContext d,
			int expected) {
		StringBuilder out = new StringBuilder();
		out.append(getPrintName(n.getOperator()));
		if (expected == PREDICATE) {
			out.append(" = TRUE");
			return new ExprReturn(out, P_equals);
		}
		return new ExprReturn(out);
	}

	/**
	 * @param n
	 * @param d
	 * @param expected
	 * @return
	 */
	protected ExprReturn visitUserdefinedOp(OpApplNode n, DContext d,
			int expected) {
		StringBuilder out = new StringBuilder();
		OpDefNode def = (OpDefNode) n.getOperator();

		// Operator ist ein B-BuiltIn-Operator
		if (BBuiltInOPs.contains(def.getName())) {
			return evalBBuiltIns(n, d, expected);
		}

		out.append(getPrintName(def));

		if (n.getArgs().length > 0) {
			out.append("(");
			for (int i = 0; i < n.getArgs().length; i++) {
				out.append(visitExprOrOpArgNode(n.getArgs()[i], d, VALUE).out);
				if (i < n.getArgs().length - 1) {
					out.append(", ");
				}
			}
			out.append(")");

		}
		BType defType = (BType) n.getToolObject(TYPE_ID);
		if (defType != null && defType.getKind() == BOOL) {
			return makeBoolValue(out, expected, P_max);
		}
		return new ExprReturn(out);
	}

	/**
	 * @param n
	 * @param d
	 * @param expected
	 * @return
	 */
	private ExprReturn evalBuiltInKind(OpApplNode n, DContext d, int expected) {
		StringBuilder out = new StringBuilder();
		switch (getOpCode(n.getOperator().getName())) {

		/**********************************************************************
		 * equality and disequality: =, #, /=
		 **********************************************************************/
		case OPCODE_eq: { // =
			out = evalOpMoreArgs(n, " = ", d, VALUE, P_equals);
			return makeBoolValue(out, expected, P_equals);
		}

		case OPCODE_noteq: // /=
		{
			out = evalOpMoreArgs(n, " /= ", d, VALUE, P_noteq);
			return makeBoolValue(out, expected, P_noteq);
		}

		/**********************************************************************
		 * Logic Operators
		 **********************************************************************/
		case OPCODE_cl: // $ConjList
		{
			for (int i = 0; i < n.getArgs().length; i++) {
				if (i == 0) {
					out.append(brackets(
							visitExprOrOpArgNode(n.getArgs()[i], d, PREDICATE),
							P_and, true));
				} else {
					out.append("\n" + d.indent + " & ");
					out.append(brackets(
							visitExprOrOpArgNode(n.getArgs()[i], d, PREDICATE),
							P_and, false));
				}
			}
			return makeBoolValue(out, expected, P_and);
		}
		case OPCODE_land: // \land
		{
			out = evalOpMoreArgs(n, " & ", d, PREDICATE, P_and);
			return makeBoolValue(out, expected, P_and);
		}
		case OPCODE_dl: // $DisjList
		{
			for (int i = 0; i < n.getArgs().length; i++) {
				if (i == 0) {
					out.append(brackets(
							visitExprOrOpArgNode(n.getArgs()[i], d, PREDICATE),
							P_or, true));
				} else {
					out.append("\n" + d.indent + " or ");
					out.append(brackets(
							visitExprOrOpArgNode(n.getArgs()[i], d, PREDICATE),
							P_or, false));
				}
			}
			return makeBoolValue(out, expected, P_or);
		}

		case OPCODE_lor: // \/
		{
			out = evalOpMoreArgs(n, " or ", d, PREDICATE, P_or);
			return makeBoolValue(out, expected, P_or);
		}
		case OPCODE_equiv: // \equiv
		{
			out = evalOpMoreArgs(n, " <=> ", d, PREDICATE, P_equiv);
			return makeBoolValue(out, expected, P_equiv);
		}
		case OPCODE_implies: // =>
		{
			out = evalOpMoreArgs(n, " => ", d, PREDICATE, P_implies);
			return makeBoolValue(out, expected, P_implies);
		}

		case OPCODE_lnot: { // \lnot
			out.append("not(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE).out);
			out.append(")");
			return makeBoolValue(out, expected, P_max);
		}

		case OPCODE_be: { // \E x \in S : P
			return evalBoundedQuantor(n, d, expected, "#");
		}

		case OPCODE_bf: { // \A x \in S : P
			return evalBoundedQuantor(n, d, expected, "!");
		}

		/**********************************************************************
		 * Set Operators
		 **********************************************************************/
		case OPCODE_se: // SetEnumeration {..}
		{
			out.append("{");
			out.append(evalOpMoreArgs(n, ", ", d, VALUE, P_comma));
			out.append("}");
			return new ExprReturn(out, P_max);
		}

		case OPCODE_in: // \in
		{
			ExprReturn r = visitExprOrOpArgNode(n.getArgs()[0], d, VALUE);
			out.append(brackets(r, P_in, true));
			out.append(" : ");
			r = visitExprOrOpArgNode(n.getArgs()[1], d, NOBOOL);
			out.append(brackets(r, P_in, false));
			return makeBoolValue(out, expected, P_in);
		}
		case OPCODE_notin: // \notin
		{
			ExprReturn r = visitExprOrOpArgNode(n.getArgs()[0], d, VALUE);
			out.append(brackets(r, P_notin, true));
			out.append(" /: ");
			r = visitExprOrOpArgNode(n.getArgs()[1], d, NOBOOL);
			out.append(brackets(r, P_notin, false));
			return makeBoolValue(out, expected, P_notin);
		}

		case OPCODE_setdiff: // set difference
		{
			out = evalOpMoreArgs(n, " - ", d, NOBOOL, P_setdiff);
			return new ExprReturn(out, P_setdiff);
		}

		case OPCODE_cup: // set union
		{
			out = evalOpMoreArgs(n, " \\/ ", d, NOBOOL, P_union);
			return new ExprReturn(out, P_union);
		}

		case OPCODE_cap: // set intersection
		{
			out = evalOpMoreArgs(n, " /\\ ", d, NOBOOL, P_intersect);
			return new ExprReturn(out, P_intersect);
		}

		case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
		{
			out = evalOpMoreArgs(n, " <: ", d, NOBOOL, P_subseteq);
			return makeBoolValue(out, expected, P_subseteq);
		}

		case OPCODE_subset: // SUBSET
		{
			out.append("POW(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case OPCODE_union: // Union - Union{{1},{2}}
		{
			out.append("union(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		/**********************************************************************
		 * Set Constructor
		 **********************************************************************/
		case OPCODE_sso: { // $SubsetOf Represents {x \in S : P}
			out.append("{");
			FormalParamNode x = n.getBdedQuantSymbolLists()[0][0];
			out.append(x.getName().toString());
			out.append("|");
			out.append(x.getName().toString());
			out.append(" : ");
			ExprNode in = n.getBdedQuantBounds()[0];
			out.append(visitExprNode(in, d, NOBOOL).out);
			out.append(" & ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE).out);
			out.append("}");
			return new ExprReturn(out);
		}

		case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
			out.append("{t_|#");
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ExprNode[] bounds = n.getBdedQuantBounds();
			for (int i = 0; i < bounds.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode p = params[i][j];
					out.append(p.getName().toString());
					if (i < bounds.length - 1 || j < params[i].length - 1)
						out.append(", ");
				}
			}
			out.append(".(");
			out.append(visitBounded(n, d));
			out.append(" & t_ = ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, VALUE).out);
			out.append(")}");
			return new ExprReturn(out);
		}
		/***********************************************************************
		 * Tuple: Tuple as Function 1..n to Set (Sequence)
		 ***********************************************************************/
		case OPCODE_tup: { // $Tuple
			out.append("[");
			out.append(evalOpMoreArgs(n, ", ", d, VALUE, P_comma));
			out.append("]");
			return new ExprReturn(out);
		}

		/***********************************************************************
		 * Cartesian Product: A \X B
		 ***********************************************************************/
		case OPCODE_cp: { // $CartesianProd A \X B \X C
			out.append(evalOpMoreArgs(n, "*", d, VALUE, P_times));
			return new ExprReturn(out, P_times);
		}

		/***********************************************************************
		 * Functions
		 ***********************************************************************/
		case OPCODE_nrfs:
		case OPCODE_fc: // Represents [x \in S |-> e].
		case OPCODE_rfs: {
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
			out.append(visitBounded(n, d));
			out.append("| ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, VALUE).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case OPCODE_fa: { // f[1]
			out.append(brackets(
					visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL), P_max,
					true));
			out.append("(");
			ExprOrOpArgNode dom = n.getArgs()[1];
			if (dom instanceof OpApplNode
					&& ((OpApplNode) dom).getOperator().getName().toString()
							.equals("$Tuple")) {
				OpApplNode domOpAppl = (OpApplNode) dom;
				for (int i = 0; i < domOpAppl.getArgs().length; i++) {
					if (i != 0)
						out.append(", ");
					out.append(visitExprOrOpArgNode(domOpAppl.getArgs()[i], d,
							VALUE).out);
				}
			} else {
				out.append(visitExprOrOpArgNode(dom, d, VALUE).out);
			}
			out.append(")");
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}

		case OPCODE_domain:
			out.append("dom(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);

		case OPCODE_sof: // [ A -> B]
		{
			out.append(evalOpMoreArgs(n, " --> ", d, NOBOOL, P_total_f));
			return new ExprReturn(out, P_total_f);
		}

		/**********************************************************************
		 * Except
		 **********************************************************************/
		case OPCODE_exc: // Except
		{
			BType t = (BType) n.getToolObject(TYPE_ID);
			if (t.getKind() == STRUCT) {
				String oldRec = visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out
						.toString();
				
				Hashtable<String, String> temp = new Hashtable<String, String>();
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode s = (StringNode) pair.getChildren()[0]
							.getChildren()[0];
					String fieldName = s.getRep().toString();
					String val = visitExprOrOpArgNode(
							(ExprOrOpArgNode) pair.getChildren()[1], d, VALUE).out
							.toString();
					String newVal = evalRecVal(t, pair, oldRec, d);
					temp.put(fieldName, val);
				}

				out.append("rec(");
				StructType st = (StructType) t;
				for (int i = 0; i < st.getFields().size(); i++) {
					String fieldName = st.getFields().get(i);
					out.append(fieldName);
					out.append(" : ");
					String value = temp.get(fieldName);
					if (value == null) {
						value = oldRec + "'" + fieldName;
					}
					out.append(value);

					if (i < st.getFields().size() - 1) {
						out.append(", ");
					}
				}
				out.append(")");
				return new ExprReturn(out);

			} else {
				// function
				out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
				out.append(" <+ {");
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					OpApplNode domSeq = (OpApplNode) pair.getArgs()[0];
					ExprOrOpArgNode domExpr = domSeq.getArgs()[0];
					if (domExpr instanceof OpApplNode
							&& ((OpApplNode) domExpr).getOperator().getName()
									.toString().equals("$Tuple")) {
						OpApplNode domOpAppl = (OpApplNode) domExpr;
						out.append("(");
						for (int j = 0; j < domOpAppl.getArgs().length; j++) {
							if (j != 0) {
								out.append(", ");
							}
							out.append(visitExprOrOpArgNode(
									domOpAppl.getArgs()[j], d, VALUE).out);
						}
						out.append(")");
					} else {
						out.append(visitExprOrOpArgNode(pair.getArgs()[0], d,
								VALUE).out);
					}
					out.append(" |-> ");
					out.append(brackets(
							visitExprOrOpArgNode(pair.getArgs()[1], d, VALUE),
							P_maplet, false));
					if (i < n.getArgs().length - 1) {
						out.append(", ");
					}
				}
				out.append("}");
				return new ExprReturn(out, P_rel_overriding);

			}
		}

		/***********************************************************************
		 * Records
		 ***********************************************************************/
		case OPCODE_sor: { // $SetOfRcds [L1 : e1, L2 : e2]
			PowerSetType pow = (PowerSetType) n.getToolObject(TYPE_ID);
			StructType struct = (StructType) pow.getSubType();
			Hashtable<String, StringBuilder> pairs = new Hashtable<String, StringBuilder>();
			ExprOrOpArgNode[] args = n.getArgs();
			for (int i = 0; i < args.length; i++) {
				OpApplNode pair = (OpApplNode) args[i];
				StringNode stringNode = (StringNode) pair.getArgs()[0];
				pairs.put(stringNode.getRep().toString(),
						visitExprOrOpArgNode(pair.getArgs()[1], d, VALUE).out);
			}
			out.append("struct(");
			for (int i = 0; i < struct.getFields().size(); i++) {
				String fieldName = struct.getFields().get(i);
				out.append(fieldName);
				out.append(" : ");
				if (pairs.containsKey(fieldName)) {
					out.append(pairs.get(fieldName));
				} else {
					out.append(struct.getType(fieldName));
				}
				if (i < struct.getFields().size() - 1)
					out.append(",");
			}
			out.append(")");
			return new ExprReturn(out, P_max);
		}

		case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
			StructType struct = (StructType) n.getToolObject(TYPE_ID);
			Hashtable<String, StringBuilder> pairs = new Hashtable<String, StringBuilder>();
			ExprOrOpArgNode[] args = n.getArgs();
			for (int i = 0; i < args.length; i++) {
				OpApplNode pair = (OpApplNode) args[i];
				StringNode stringNode = (StringNode) pair.getArgs()[0];
				pairs.put(stringNode.getRep().toString(),
						visitExprOrOpArgNode(pair.getArgs()[1], d, VALUE).out);
			}
			out.append("rec(");
			for (int i = 0; i < struct.getFields().size(); i++) {
				String fieldName = struct.getFields().get(i);
				out.append(fieldName);
				out.append(" : ");
				if (pairs.containsKey(fieldName)) {
					out.append(pairs.get(fieldName));
				} else {
					out.append(getDummy(struct.getType(fieldName)));
				}
				if (i < struct.getFields().size() - 1)
					out.append(",");
			}
			out.append(")");
			return new ExprReturn(out, P_max);
		}

		case OPCODE_rs: { // $RcdSelect r.c
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append("'");
			StringNode stringNode = (StringNode) n.getArgs()[1];
			out.append(stringNode.getRep().toString());
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out, P_record_acc);
		}

		/***********************************************************************
		 * miscellaneous constructs
		 ***********************************************************************/
		case OPCODE_ite: // IF THEN ELSE
		{
			return evalIfThenElse(n, d, expected);

		}

		case OPCODE_case: { // CASE p1 -> e1 [] p2 -> e2
			out.append("(");
			StringBuilder all = new StringBuilder();
			for (int i = 0; i < n.getArgs().length; i++) {
				OpApplNode pair = (OpApplNode) n.getArgs()[i];
				out.append("%t_.(t_ = 0 & ");
				if (pair.getArgs()[0] == null) {
					out.append("not(" + all + ")");
				} else {
					ExprReturn p = visitExprOrOpArgNode(pair.getArgs()[0], d,
							PREDICATE);
					if (i != 0) {
						all.append(" or ");
					}
					all.append(brackets(p, P_or, i == 0));
					out.append(brackets(p, P_and, false));
				}
				out.append(" | ");
				out.append(visitExprOrOpArgNode(pair.getArgs()[1], d, VALUE).out);
				out.append(")");
				if (i < n.getArgs().length - 1) {
					out.append(" \\/ ");
				}
			}
			out.append(")(0)");
			return new ExprReturn(out);
		}

		case OPCODE_bc: { // CHOOSE x \in S: P
			out.append("CHOOSE({");
			FormalParamNode x = n.getBdedQuantSymbolLists()[0][0];
			out.append(x.getName().toString());
			out.append("|");
			out.append(x.getName().toString());
			out.append(" : ");
			ExprNode in = n.getBdedQuantBounds()[0];
			out.append(visitExprNode(in, d, NOBOOL).out);
			out.append(" & ");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE).out);
			out.append("})");
			return new ExprReturn(out);

		}

		/***********************************************************************
		 * UNCHANGED
		 ************************************************************************/
		case OPCODE_unchanged:
			Boolean b = (Boolean) n.getToolObject(USED);
			if (b != null) {
				return new ExprReturn("TRUE = TRUE", P_equals);
			}
			OpApplNode k = (OpApplNode) n.getArgs()[0];
			if (k.getOperator().getKind() == VariableDeclKind) {
				String name = k.getOperator().getName().toString();
				out.append(name + "_n = " + name);
			} else {
				// Tuple
				for (int i = 0; i < k.getArgs().length; i++) {
					String name = visitExprOrOpArgNode(k.getArgs()[i], d, VALUE).out
							.toString();
					out.append(name + "_n = " + name);
					if (i < k.getArgs().length - 1) {
						out.append(" & ");
					}
				}
			}
			return new ExprReturn(out);

			/***********************************************************************
			 * Prime
			 ***********************************************************************/
		case OPCODE_prime: // prime
		{
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, VALUE).out);
			out.append("_n");
			return new ExprReturn(out);
		}

		/***********************************************************************
		 * Sany internal
		 ***********************************************************************/
		case OPCODE_seq: // !
		{
			return visitExprOrOpArgNode(n.getArgs()[0], d, expected);
		}

		/***********************************************************************
		 * no TLA+ Built-ins
		 ***********************************************************************/
		case 0: {
			return evalBBuiltIns(n, d, expected);
		}

		case OPCODE_sa: // []_
		case OPCODE_box: // []
		case OPCODE_diamond: // <>
		case OPCODE_wf: // weak fairness
		{
			throw new RuntimeException("Not supported operator: "
					+ n.toString(2));
		}

		}
		throw new RuntimeException(n.toString(2));
	}

	/**
	 * @param t
	 * @param pair
	 * @return
	 */
	private String evalRecVal(BType t, OpApplNode pair, String oldRec, DContext d) {
		ExprOrOpArgNode first = pair.getArgs()[0];
		ExprOrOpArgNode second = pair.getArgs()[1];
		
		OpApplNode seq = (OpApplNode) first;
		if(seq.getArgs().length == 1){
			String val = visitExprOrOpArgNode(
					(ExprOrOpArgNode) pair.getChildren()[1], d, VALUE).out
					.toString();
			return val;
		}
		StringNode s1 = (StringNode) seq.getArgs()[0];
		String field1 = s1.getRep().toString();
		
		StructType sType = (StructType) t;
		BType field1Type = sType.getType(field1);
		//System.out.println(seq.toString(2));
		return null;
	}

	/**
	 * @param n
	 * @return
	 */
	protected ExprReturn evalIfThenElse(OpApplNode n, DContext d, int expected) {
		BType t = (BType) n.getToolObject(TYPE_ID);

		if (t.getKind() == BOOL) {
			d.indent.append(" ");
			ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE);
			ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d, PREDICATE);
			ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d,
					PREDICATE);
			String res = String.format(
					"(%s \n%s => %s) \n\t & (not(%s) \n%s => %s)",
					brackets(iif, P_implies, true), d.indent,
					brackets(then, P_implies, false), iif.out, d.indent,
					brackets(eelse, P_implies, false));
			return makeBoolValue(new StringBuilder(res), expected, P_and);
		} else {
			// ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d,
			// PREDICATE);
			// ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d,
			// VALUE);
			// ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d,
			// VALUE);
			// String res = String
			// .format("(%%t_.( t_ = 0 & %s | %s )\\/%%t_.( t_ = 0 & not(%s) | %s ))(0)",
			// iif.out, then.out, iif.out, eelse.out);
			// return new ExprReturn(res);
			ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d, VALUE);
			ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d, VALUE);
			ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d, VALUE);
			String res = String.format("IF_THEN_ELSE(%s, %s, %s)", iif.out,
					then.out, eelse.out);
			return new ExprReturn(res);
		}
	}

	private ExprReturn evalBoundedQuantor(OpApplNode n, DContext d,
			int expected, String symbol) {
		StringBuilder out = new StringBuilder();
		out.append(symbol);
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		for (int i = 0; i < params.length; i++) {
			for (int j = 0; j < params[i].length; j++) {
				out.append(params[i][j].getName());
				if (j < params[i].length - 1) {
					out.append(",");
				}
			}
			if (i < params.length - 1) {
				out.append(",");
			}
		}
		out.append(".(");
		out.append(visitBounded(n, d));
		out.append(symbol.equals("#") ? " & " : " => ");
		out.append(brackets(visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE),
				symbol.equals("#") ? P_and : P_implies, false));
		out.append(")");
		return makeBoolValue(out, expected, P_max);
	}

	@SuppressWarnings("unused")
	private ExprReturn evalStructOrRec(String string, OpApplNode n, DContext d) {
		StringBuilder out = new StringBuilder();
		out.append(string);
		out.append("(");
		ExprOrOpArgNode[] args = n.getArgs();
		for (int i = 0; i < args.length; i++) {
			OpApplNode pair = (OpApplNode) args[i];
			StringNode stringNode = (StringNode) pair.getArgs()[0];
			out.append(stringNode.getRep().toString());
			out.append(" : ");
			out.append(visitExprOrOpArgNode(pair.getArgs()[1], d, VALUE).out);
			if (i != args.length - 1)
				out.append(", ");
		}
		out.append(")");
		return new ExprReturn(out, P_max);
	}

	protected ExprReturn evalBBuiltIns(OpApplNode n, DContext d, int expected) {
		StringBuilder out = new StringBuilder();

		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {

		/**********************************************************************
		 * Standard Module Naturals
		 **********************************************************************/
		case B_OPCODE_nat: // Nat
		{
			out.append("NATURAL");
			return new ExprReturn(out);
		}

		case B_OPCODE_plus: // +
			out.append(evalOpMoreArgs(n, " + ", d, NOBOOL, P_plus));
			return new ExprReturn(out, P_plus);

		case B_OPCODE_minus: // -
		{
			out.append(evalOpMoreArgs(n, " - ", d, NOBOOL, P_minus));
			return new ExprReturn(out, P_minus);
		}

		case B_OPCODE_times: // *
		{
			out.append(evalOpMoreArgs(n, " * ", d, NOBOOL, P_times));
			return new ExprReturn(out, P_times);
		}

		case B_OPCODE_exp: // x^y
		{
			out.append(evalOpMoreArgs(n, " ** ", d, NOBOOL, P_exp));
			return new ExprReturn(out, P_exp);
		}

		case B_OPCODE_lt: // <
		{
			out.append(evalOpMoreArgs(n, " < ", d, NOBOOL, P_lt));
			return makeBoolValue(out, expected, P_lt);
		}

		case B_OPCODE_gt: // >
		{
			out.append(evalOpMoreArgs(n, " > ", d, NOBOOL, P_gt));
			return makeBoolValue(out, expected, P_gt);
		}

		case B_OPCODE_leq: // <=
		{
			out.append(evalOpMoreArgs(n, " <= ", d, NOBOOL, P_leq));
			return makeBoolValue(out, expected, P_leq);
		}

		case B_OPCODE_geq: // >=
		{
			out.append(evalOpMoreArgs(n, " >= ", d, NOBOOL, P_geq));
			return makeBoolValue(out, expected, P_geq);
		}

		case B_OPCODE_mod: // modulo
		{
			out.append(evalOpMoreArgs(n, " mod ", d, NOBOOL, P_mod));
			return new ExprReturn(out, P_mod);
		}

		case B_OPCODE_div: // /
		{
			out.append(evalOpMoreArgs(n, " / ", d, NOBOOL, P_div));
			return new ExprReturn(out, P_div);
		}

		case B_OPCODE_dotdot: // ..
		{
			out.append(evalOpMoreArgs(n, " .. ", d, NOBOOL, P_dotdot));
			return new ExprReturn(out, P_dotdot);
		}

		/**********************************************************************
		 * Standard Module Integers
		 **********************************************************************/
		case B_OPCODE_int: // Int
		{
			out.append("INTEGER");
			return new ExprReturn(out);
		}

		case B_OPCODE_uminus: // -x
		{
			out.append("-");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			return new ExprReturn(out, P_uminus);
		}

		/**********************************************************************
		 * Standard Module FiniteSets
		 **********************************************************************/
		case B_OPCODE_card: // Cardinality
		{
			out.append("card(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_finite: { // IsFiniteSet
			ExprReturn exprr = visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL);
			// String res = String
			// .format("#seq_.(seq_ : seq(%s) & !s.(s : %s => #n.(n : 1 .. size(seq_) & seq_(n) = s)))",
			// exprr.out, exprr.out);
			String res = String.format("%s : FIN(%s)", exprr.out, exprr.out);
			out.append(res);
			return makeBoolValue(out, expected, P_max);
		}

		/**********************************************************************
		 * Standard Module Sequences
		 **********************************************************************/
		case B_OPCODE_seq: { // Seq(S) - set of sequences
			out.append("seq(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_len: { // length of the sequence
			out.append("size(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_conc: { // s \o s2 - concatenation of s and s2
			out.append(evalOpMoreArgs(n, " ^ ", d, NOBOOL, P_conc));
			return new ExprReturn(out, P_conc);
		}

		case B_OPCODE_append: { // Append(s,x)
			out.append(evalOpMoreArgs(n, " <- ", d, NOBOOL, P_append));
			return new ExprReturn(out, P_append);
		}

		case B_OPCODE_head: { // Head(s)
			out.append("first(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_tail: { // Tail(s)
			out.append("tail(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_subseq: { // SubSeq(s,m,n)
			StringBuilder s = visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out;
			out.append("(");
			out.append(s);
			out.append("/|\\"); // taking first n elements
			out.append(visitExprOrOpArgNode(n.getArgs()[2], d, NOBOOL).out);
			out.append(")\\|/"); // dropping first m-1 elements
			out.append(visitExprOrOpArgNode(n.getArgs()[1], d, NOBOOL).out);
			out.append("-1");
			return new ExprReturn(out, P_drop_last);
		}

		/**********************************************************************
		 * Standard Module Sequences
		 **********************************************************************/
		case B_OPCODE_min: { // MinOfSet(s)
			out.append("min(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_max: { // MaxOfSet(s)
			out.append("max(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		case B_OPCODE_setprod: { // SetProduct(s)
			out.append("PI(z_).(z_:");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append("|z_)");
			return new ExprReturn(out);
		}

		case B_OPCODE_setsum: { // SetSummation(s)
			out.append("SIGMA(z_).(z_:");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append("|z_)");
			return new ExprReturn(out);
		}

		case B_OPCODE_permseq: { // PermutedSequences(s)
			out.append("perm(");
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
			out.append(")");
			return new ExprReturn(out);
		}

		/***********************************************************************
		 * TLA+ Built-Ins, but not in tlc.tool.BuiltInOPs
		 ***********************************************************************/
		case B_OPCODE_bool: // BOOLEAN
			out.append("BOOL");
			return new ExprReturn(out);

		case B_OPCODE_true: // TRUE
			out.append("TRUE");
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);

		case B_OPCODE_false: // FALSE
			out.append("FALSE");
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);

		case B_OPCODE_string: // STRING
			out.append("STRING");
			return new ExprReturn(out);

		}

		throw new RuntimeException(n.toString(2));
	}

	protected StringBuilder visitBounded(OpApplNode n, DContext d) {
		StringBuilder out = new StringBuilder();
		FormalParamNode[][] nodes = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		for (int i = 0; i < nodes.length; i++) {
			for (int j = 0; j < nodes[i].length; j++) {
				out.append(nodes[i][j].getName());
				out.append(" : ");
				out.append(visitExprNode(in[i], d, NOBOOL).out);
				if (j < nodes[i].length - 1 || i < nodes.length - 1) {
					out.append(" & ");
				}
			}
		}
		return out;
	}

	protected StringBuilder evalOpMoreArgs(OpApplNode n, String operator,
			DContext d, int expected, int priority) {
		StringBuilder out = new StringBuilder();
		ExprOrOpArgNode[] args = n.getArgs();
		for (int i = 0; i < args.length; i++) {
			ExprReturn r = visitExprOrOpArgNode(args[i], d, expected);
			if (i == 0) {
				out.append(brackets(r, priority, true));
			} else {
				out.append(operator);
				out.append(brackets(r, priority, false));
			}

		}
		return out;
	}

	protected ExprReturn makeBoolValue(StringBuilder out, int expected,
			int priority) {
		StringBuilder res = new StringBuilder();
		if (expected == VALUE) {
			res.append("bool(" + out + ")");
			return new ExprReturn(res);
		} else {
			return new ExprReturn(out, priority);
		}
	}

	protected StringBuilder brackets(ExprReturn r, int p, boolean left) {
		StringBuilder res = new StringBuilder();
		if ((left && r.getPriority() < p) || (!left && r.getPriority() <= p)) {
			res.append("(");
			res.append(r.getOut());
			res.append(")");
		} else
			res.append(r.getOut());
		return res;
	}

	protected String getPrintName(SymbolNode node) {
		if (node.getToolObject(NEW_NAME) != null) {
			return (String) node.getToolObject(NEW_NAME);
		} else {
			return node.getName().toString();
		}
	}

	private String getDummy(BType type) {
		switch (type.getKind()) {
		case INTEGER:
			return "0";

		case STRING:
			return "\"\"";

		case POW:
			return "{}";

		case BOOL:
			return "FALSE";
		case MODELVALUE:
			EnumType e = (EnumType) type;
			return "noVal" + e.id;
		default:
			break;
		}
		return null;

	}
}
