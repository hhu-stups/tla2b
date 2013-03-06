/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;


import java.util.ArrayList;
import java.util.LinkedHashMap;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class BOperation implements ASTConstants, ToolGlobals, TranslationGlobals {
	private String name;
	private ExprNode node;
	private ArrayList<OpApplNode> existQuans;
	private ArrayList<String> opParams;
	private ArrayList<String> unchangedVariables;

	public BOperation(String name, ExprNode n,
			ArrayList<OpApplNode> existQuans) {
		this.name = name;
		this.node = n;
		this.existQuans = existQuans;
		evalParams();
		findUnchangedVariables();
	}

	private void evalParams() {
		opParams = new ArrayList<String>();
		for (int i = 0; i < existQuans.size(); i++) {
			OpApplNode n = existQuans.get(i);
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			for (int k = 0; k < params.length; k++) {
				for (int j = 0; j < params[k].length; j++) {
					opParams.add(params[k][j].getName().toString());
				}
			}
		}
	}

	public String getName() {
		return name;
	}

	public ExprNode getNode() {
		return node;
	}

	public ArrayList<OpApplNode> getExistQuans() {
		return new ArrayList<OpApplNode>(existQuans);
	}

	public ArrayList<String> getOpParams() {
		return opParams;
	}

	public ArrayList<String> getUnchangedVariables(){
		return unchangedVariables;
	}
	
	private void findUnchangedVariables() {
		unchangedVariables = new ArrayList<String>();
		findUnchangedVaribalesInSemanticNode(node);
	}
	

	/**
	 * @param node2
	 */
	private void findUnchangedVaribalesInSemanticNode(SemanticNode node) {
		switch (node.getKind()) {
		case OpApplKind: {
			findUnchangedVariablesInOpApplNode((OpApplNode) node);
			return;
		}
		case LetInKind: {
			LetInNode letNode = (LetInNode) node;
			findUnchangedVaribalesInSemanticNode(letNode.getBody());
			return;
		}

		case SubstInKind: {
			SubstInNode substInNode = (SubstInNode) node;
			findUnchangedVaribalesInSemanticNode(substInNode.getBody());
			return;
		}
		}
	}

	/**
	 * @param node2
	 */
	private void findUnchangedVariablesInOpApplNode(OpApplNode n) {

		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind
				&& !BBuiltInOPs.contains(n.getOperator().getName())) {
			OpDefNode def = (OpDefNode) n.getOperator();
			findUnchangedVaribalesInSemanticNode(def.getBody());
			return;
		} else if (kind == BuiltInKind) {
			int opcode = BuiltInOPs.getOpCode(n.getOperator().getName());
			switch (opcode) {
			case OPCODE_land: // \land
			case OPCODE_cl: { // $ConjList
				for (int i = 0; i < n.getArgs().length; i++) {
					findUnchangedVaribalesInSemanticNode(n.getArgs()[i]);
				}
				return;
			}
			case OPCODE_unchanged:{
				n.setToolObject(USED, false);
				OpApplNode k = (OpApplNode) n.getArgs()[0];
				if (k.getOperator().getKind() == VariableDeclKind) {
					String name = k.getOperator().getName().toString();
					unchangedVariables.add(name);
				} else {
					// Tuple
					for (int i = 0; i < k.getArgs().length; i++) {
						OpApplNode var = (OpApplNode) k.getArgs()[i];
						String name = var.getOperator().getName().toString();
						unchangedVariables.add(name);
					}
				}
			}
			
			}
		}
	}
	
	
}
