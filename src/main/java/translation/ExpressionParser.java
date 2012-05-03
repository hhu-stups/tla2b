/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;

import exceptions.MyException;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AbortException;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import util.ToolIO;

public class ExpressionParser implements SyntaxTreeConstants {
	private String expr;
	private ArrayList<String> constants;
	private ArrayList<String> boundedVariables;

	public ExpressionParser(String expr) throws exceptions.FrontEndException,
			MyException, AbortException {
		this.expr = expr;

		String module = "----MODULE Test----\n" + "EXTENDS Naturals\n"
				+ "def123 == " + expr + "\n====";

		SpecObj spec = parseModuleWithoutSemanticAnalyse(module);

		evalConstants(spec);
		StringBuilder sb = new StringBuilder();
		sb.append("----MODULE Test----\n");
		sb.append("EXTENDS Naturals\n");
		sb.append("def123");
		if (constants.size() > 0) {
			sb.append("(");
			for (int i = 0; i < constants.size(); i++) {
				if (i != 0) {
					sb.append(", ");
				}
				sb.append(constants.get(i));
			}
			sb.append(")");
		}
		sb.append(" == ");
		sb.append(expr);
		sb.append("\n====================");
		// System.out.println(sb);
		StringBuilder res = Main.start(sb.toString(), null, true);
		System.out.println(res);
	}

	/**
	 * @param module
	 * @throws exceptions.FrontEndException
	 */
	private SpecObj parseModuleWithoutSemanticAnalyse(String module)
			throws exceptions.FrontEndException {
		//SANY.turnSemanticAnalyseOff();
		SpecObj spec = new SpecObj(module, null);
		try {
			SANY.frontEndMain(spec, module, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
		}

		if (spec.parseErrors.isFailure()) {
			throw new exceptions.FrontEndException(
					Main.allMessagesToString(ToolIO.getAllMessages())
							+ spec.semanticErrors, spec);
		}
		//SANY.turnSemanticAnalyseOn();
		return spec;
	}

	/**
	 * @param spec
	 * @return
	 */
	private void evalConstants(SpecObj spec) {
		constants = new ArrayList<String>();
		boundedVariables = new ArrayList<String>();
		ParseUnit p = (ParseUnit) spec.parseUnitContext.get("Testing");
		TreeNode n_module = p.getParseTree();
		TreeNode n_body = n_module.heirs()[2];
		TreeNode n_operatorDefintion = n_body.heirs()[0];
		TreeNode expr = n_operatorDefintion.heirs()[2];
		searchVarInSyntaxTree(expr);

		for (int i = 0; i < boundedVariables.size(); i++) {
			constants.remove(boundedVariables.get(i));
		}

	}

	/**
	 * 
	 */
	private void searchVarInSyntaxTree(TreeNode treeNode) {
		switch (treeNode.getKind()) {
		case N_GeneralId: {
			String con = treeNode.heirs()[1].getImage();
			if (!constants.contains(con)) {
				constants.add(con);
			}
			return;
		}
		case N_QuantBound: {
			TreeNode[] children = treeNode.heirs();
			for (int i = 0; i < children.length - 2; i = i + 2) {
				String boundedVar = children[i].getImage();
				if (!boundedVariables.contains(boundedVar)) {
					boundedVariables.add(boundedVar);
				}
			}
			searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
		}
		case N_SubsetOf:{ // { x \in S : e }
			TreeNode[] children = treeNode.heirs();
			String boundedVar = children[1].getImage(); // x
			if (!boundedVariables.contains(boundedVar)) {
				boundedVariables.add(boundedVar);
			}
			searchVarInSyntaxTree(treeNode.heirs()[3]); // S
			searchVarInSyntaxTree(treeNode.heirs()[5]); // e
		}
		
		}

		for (int i = 0; i < treeNode.heirs().length; i++) {
			searchVarInSyntaxTree(treeNode.heirs()[i]);
		}
	}
}
