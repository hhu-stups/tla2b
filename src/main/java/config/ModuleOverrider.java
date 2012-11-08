/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package config;

import java.util.Hashtable;


import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;

public class ModuleOverrider extends BuiltInOPs implements ASTConstants {

	private ModuleNode moduleNode;
	private Hashtable<OpDeclNode, OpDefNode> constantOverrideTable;
	private Hashtable<OpDefNode, OpDefNode> operatorOverrideTable;
	private Hashtable<OpDefNode, ValueObj> operatorAssignments;

	/**
	 * @param constantOverrideTable
	 * @param operatorOverrideTable
	 */
	public ModuleOverrider(ModuleNode moduleNode,
			Hashtable<OpDeclNode, OpDefNode> constantOverrideTable,
			Hashtable<OpDefNode, OpDefNode> operatorOverrideTable,
			Hashtable<OpDefNode, ValueObj> operatorAssignments) {
		this.moduleNode = moduleNode;
		this.constantOverrideTable = constantOverrideTable;
		this.operatorOverrideTable = operatorOverrideTable;
		this.operatorAssignments = operatorAssignments;
	}

	/**
	 * @param moduleNode2
	 * @param conEval
	 */
	public ModuleOverrider(ModuleNode moduleNode, ConfigfileEvaluator conEval) {
		this.moduleNode = moduleNode;
		this.constantOverrideTable = conEval.getConstantOverrideTable();
		this.operatorOverrideTable = conEval.getOperatorOverrideTable();
		this.operatorAssignments = conEval.getOperatorAssignments();
	}

	public void start() {
		OpDefNode[] defs = moduleNode.getOpDefs();
		for (int i = 0; i < defs.length; i++) {
			OpDefNode def = defs[i];
			if (operatorAssignments.containsKey(def)) {
				ExprNode oldExpr = def.getBody();
				TLCValueNode valueNode = new TLCValueNode(
						operatorAssignments.get(def), oldExpr.getTreeNode());
				def.setBody(valueNode);
			}else if(operatorAssignments.containsKey(def.getSource())){
				ExprNode oldExpr = def.getBody();
				TLCValueNode valueNode = new TLCValueNode(
						operatorAssignments.get(def .getSource()), oldExpr.getTreeNode());
				def.setBody(valueNode);
			}
			
		}

		for (int i = 0; i < defs.length; i++) {
			visitExprNode(defs[i].getBody());
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			visitExprNode(assumes[i].getAssume());
		}
	}

	private void visitExprOrOpArgNode(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			visitExprNode((ExprNode) n);
			return;
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	/**
	 * @param body
	 */
	private void visitExprNode(ExprNode n) {

		switch (n.getKind()) {
		case OpApplKind:
			visitOpApplNode((OpApplNode) n);
			return;

		case StringKind:
		case AtNodeKind: // @
		case NumeralKind: {
			return;
		}

		case LetInKind: {
			LetInNode l = (LetInNode) n;
			for (int i = 0; i < l.getLets().length; i++) {
				visitExprNode(l.getLets()[i].getBody());
			}
			visitExprNode(l.getBody());
			return;
		}
		}
	}

	/**
	 * @param n
	 */
	private void visitOpApplNode(OpApplNode n) {
		SymbolNode s = n.getOperator();

		switch (s.getKind()) {
		case ConstantDeclKind: {
			if (constantOverrideTable.containsKey(s)) {
				n.setOperator(constantOverrideTable.get(s));
			}
			break;

		}
		case FormalParamKind: // Params are not global in the modul
		case VariableDeclKind: // TODO try to override variable
			break;
		
		case BuiltInKind:// Buildin operator can not be overridden by in the
							// configuration file
			ExprNode[] ins = n.getBdedQuantBounds();
			for (int i = 0; i < ins.length; i++) {
				visitExprOrOpArgNode(ins[i]);
			}
			break;

		case UserDefinedOpKind: {
			if (operatorOverrideTable.containsKey(s)) {
				n.setOperator(operatorOverrideTable.get(s));
			}
			break;
		}
		}
		for (int i = 0; i < n.getArgs().length; i++) {
			if(n.getArgs()[i] != null)
				visitExprOrOpArgNode(n.getArgs()[i]);
		}
		return;
	}

}
