/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.pprint;


import java.util.Hashtable;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.types.TLAType;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;

public class ExpressionPrinter extends AbstractExpressionPrinter {

	private Hashtable<FormalParamNode, ExprOrOpArgNode> paramterSubstitution;
	private ModuleNode moduleNode;
	private StringBuilder BExpression;

	public ExpressionPrinter(ModuleNode n) {
		this.moduleNode = n;
		paramterSubstitution = new Hashtable<FormalParamNode, ExprOrOpArgNode>();
	}

	public void start() {
		OpDefNode[] defs = moduleNode.getOpDefs();
		ExprReturn e = visitExprNode(defs[defs.length - 1].getBody(),
				new DContext(), VALUEORPREDICATE);
		BExpression = e.out;
	}

	public StringBuilder getBExpression() {
		return BExpression;
	}

	@Override
	protected ExprReturn visitUserdefinedOp(OpApplNode n, DContext d,
			int expected) {
		OpDefNode def = (OpDefNode) n.getOperator();
		if (BBuiltInOPs.contains(def.getName())) {
			return evalBBuiltIns(n, d, expected);
		}

		// substitute the parameters and inline the boby of the operator
		FormalParamNode[] params = def.getParams();
		if (params.length > 0) {
			for (int i = 0; i < n.getArgs().length; i++) {
				this.paramterSubstitution.put(params[i], n.getArgs()[i]);
			}
		}
		return visitExprNode(def.getBody(), new DContext(), expected);
	}

	@Override
	protected ExprReturn evalIfThenElse(OpApplNode n, DContext d, int expected) {
		TLAType t = (TLAType) n.getToolObject(TYPE_ID);

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
			ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d, PREDICATE);
			ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d, VALUE);
			ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d, VALUE);
			String res = String
					.format("(%%t_.( t_ = 0 & %s | %s )\\/%%t_.( t_ = 0 & not(%s) | %s ))(0)",
							iif.out, then.out, iif.out, eelse.out);
			return new ExprReturn(res);
		}
	}

	@Override
	protected ExprReturn visitFormalParamNode(OpApplNode n, DContext d,
			int expected) {
		StringBuilder out = new StringBuilder();
		ExprOrOpArgNode e = paramterSubstitution.get((FormalParamNode) n
				.getOperator());
		if (e != null) {
			return visitExprOrOpArgNode(e, d, expected);
		}
		out.append(getPrintName(n.getOperator()));
		if (expected == PREDICATE) {
			out.append(" = TRUE");
			return new ExprReturn(out, P_equals);
		}
		return new ExprReturn(out);
	}

}
