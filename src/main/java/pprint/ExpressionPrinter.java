/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package pprint;

import global.BBuiltInOPs;

import java.util.ArrayList;
import java.util.Hashtable;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;

public class ExpressionPrinter extends AbstractExpressionPrinter {

	private ArrayList<OpDefNode> letInNodeList;
	private Hashtable<FormalParamNode, ExprOrOpArgNode> paramterSubstitution;
	private ModuleNode moduleNode;
	private StringBuilder BExpression;

	public ExpressionPrinter(ModuleNode n) {
		this.moduleNode = n;
		paramterSubstitution = new Hashtable<FormalParamNode, ExprOrOpArgNode>();
	}
	
	public void start(){
		OpDefNode[] defs = moduleNode.getOpDefs();
		ExprReturn e = visitExprNode(defs[defs.length - 1].getBody(),
				new DContext(), VALUEORPREDICATE);
		BExpression = e.out;
	}

	public StringBuilder getBExpression(){
		return BExpression;
	}
	
	@Override
	protected ExprReturn visitUserdefinedOp(OpApplNode n, DContext d,
			int expected) {
		StringBuilder out = new StringBuilder();
		OpDefNode def = (OpDefNode) n.getOperator();
		if (BBuiltInOPs.contains(def.getName())) {
			return evalBBuiltIns(n, d, expected);
		}

		out.append(getPrintName(def));

		FormalParamNode[] params = def.getParams();
		if (params.length > 0) {
			for (int i = 0; i < n.getArgs().length; i++) {
				this.paramterSubstitution.put(params[i], n.getArgs()[i]);
			}
		}
		return visitExprNode(def.getBody(), new DContext(), expected);
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
