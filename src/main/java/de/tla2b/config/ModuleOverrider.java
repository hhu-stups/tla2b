/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.config;

import java.util.Hashtable;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AbortException;
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
				TLCValueNode valueNode;
				try {
					valueNode = new TLCValueNode(operatorAssignments.get(def),
							oldExpr.getTreeNode());
				} catch (AbortException e) {
					throw new RuntimeException();
				}
				def.setBody(valueNode);
			} else if (operatorAssignments.containsKey(def.getSource())) {
				ExprNode oldExpr = def.getBody();
				TLCValueNode valueNode;
				try {
					valueNode = new TLCValueNode(operatorAssignments.get(def
							.getSource()), oldExpr.getTreeNode());
				} catch (AbortException e) {
					throw new RuntimeException();
				}
				def.setBody(valueNode);
			}

		}

		for (int i = 0; i < defs.length; i++) {
			OpApplNode res = visitExprNode(defs[i].getBody());
			if (res != null) {
				defs[i].setBody(res);
			}
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			AssumeNode assume = assumes[i];
			OpApplNode res = visitExprNode(assume.getAssume());
			if (res != null) {

				AssumeNode newAssume = new AssumeNode(assume.stn, res, null,
						null);
				assumes[i] = newAssume;
			}
		}
	}

	private OpApplNode visitExprOrOpArgNode(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {

			return visitExprNode((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	/**
	 * @param body
	 */
	private OpApplNode visitExprNode(ExprNode n) {

		switch (n.getKind()) {
		case OpApplKind:
			return (OpApplNode) visitOpApplNode((OpApplNode) n);

		case StringKind:
		case AtNodeKind: // @
		case NumeralKind: {
			return null;
		}

		case LetInKind: {
			LetInNode l = (LetInNode) n;
			for (int i = 0; i < l.getLets().length; i++) {
				visitExprNode(l.getLets()[i].getBody());
			}

			OpApplNode res = visitExprNode(l.getBody());
			if (res != null) {
				throw new RuntimeException();
			}
			return null;
		}
		}
		return null;
	}

	/**
	 * @param n
	 */
	private OpApplNode visitOpApplNode(OpApplNode n) {
		SymbolNode s = n.getOperator();
		switch (s.getKind()) {
		case ConstantDeclKind: {
			if (constantOverrideTable.containsKey(s)) {
				SymbolNode newOperator = constantOverrideTable.get(s);
				OpApplNode newNode = null;
				try {
					newNode = new OpApplNode(newOperator, n.getArgs(),
							n.getTreeNode(), null);
				} catch (AbortException e) {
					throw new RuntimeException();
				}
				for (int i = 0; i < n.getArgs().length; i++) {
					if (n.getArgs()[i] != null) {
						OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
						if (res != null) {
							n.getArgs()[i] = res;
						}
					}

				}
				// n.setOperator(constantOverrideTable.get(s));
				return newNode;
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

				OpApplNode res = visitExprOrOpArgNode(ins[i]);
				if (res != null) {
					ins[i] = res;
				}
			}
			break;

		case UserDefinedOpKind: {
			if (operatorOverrideTable.containsKey(s)) {
				SymbolNode newOperator = operatorOverrideTable.get(s);
				OpApplNode newNode = null;
				OpDefNode def = (OpDefNode) n.getOperator();
				try {
					newNode = new OpApplNode(newOperator, n.getArgs(),
							n.getTreeNode(), def.getOriginallyDefinedInModuleNode());
				} catch (AbortException e) {
					e.printStackTrace();
				}

				for (int i = 0; i < n.getArgs().length; i++) {
					if (n.getArgs()[i] != null) {
						OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
						if (res != null) {
							n.getArgs()[i] = res;
						}
					}

				}
				// n.setOperator(constantOverrideTable.get(s));
				return newNode;
			}
			break;
		}
		}

		for (int i = 0; i < n.getArgs().length; i++) {
			if (n.getArgs()[i] != null) {
				OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
				if (res != null) {
					n.getArgs()[i] = res;
				}
			}

		}
		return null;
	}

}
