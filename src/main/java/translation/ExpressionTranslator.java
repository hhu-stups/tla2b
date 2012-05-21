/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;

import pprint.ExpressionPrinter;
import analysis.NewTypeChecker;

import exceptions.TLA2BException;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import util.ToolIO;

public class ExpressionTranslator implements SyntaxTreeConstants {
	private String TLAExpression;
	private ArrayList<String> constants;
	private ArrayList<String> boundedVariables;
	private StringBuilder BExpression;

	public static String translateExpression(String bExpression)
			throws TLA2BException {
		ExpressionTranslator et = new ExpressionTranslator(bExpression);
		et.start();
		return et.BExpression.toString();
	}

	public ExpressionTranslator(String TLAExpression) {
		this.TLAExpression = TLAExpression;
		this.constants = new ArrayList<String>();
		this.boundedVariables = new ArrayList<String>();
	}

	public void start() throws TLA2BException {
		String module = "----MODULE Test----\n" + "EXTENDS Naturals\n"
				+ "foo == " + TLAExpression + "\n====";

		SpecObj spec = parseModuleWithoutSemanticAnalyse(module);

		evalConstants(spec);
		StringBuilder sb = new StringBuilder();
		sb.append("----MODULE Test----\n");
		sb.append("EXTENDS Naturals\n");
		sb.append("foo");
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
		sb.append(TLAExpression);
		sb.append("\n====================");
		// System.out.println(sb);
		BExpression = translate(sb.toString());
	}

	private static StringBuilder translate(String expr)
			throws exceptions.FrontEndException, TLA2BException {
		ModuleNode moduleNode = Main.parseModule(expr);

		NewTypeChecker tc = new NewTypeChecker(moduleNode);
		tc.start();

		ExpressionPrinter p = new ExpressionPrinter(moduleNode);
		p.start();
		return p.getBExpression();

	}

	/**
	 * @param module
	 * @throws exceptions.FrontEndException
	 */
	private SpecObj parseModuleWithoutSemanticAnalyse(String module)
			throws exceptions.FrontEndException {
		// SANY.turnSemanticAnalyseOff();
		SpecObj spec = new SpecObj(module, null);
		try {
			SANY.frontEndMain(spec, module, ToolIO.out);
		} catch (FrontEndException e) {
			throw new exceptions.FrontEndException(e.getLocalizedMessage());
			// Error in Frontend, should never happens
		}

		if (spec.parseErrors.isFailure()) {
			System.out.println("foo--------------------------");
			throw new exceptions.FrontEndException(
					Main.allMessagesToString(ToolIO.getAllMessages())
							+ spec.semanticErrors, spec);
		}
		// SANY.turnSemanticAnalyseOn();
		return spec;
	}

	/**
	 * @param spec
	 * @return
	 */
	private void evalConstants(SpecObj spec) {
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
			break;
		}
		case N_UnboundQuant: {
			TreeNode[] children = treeNode.heirs();
			for (int i = 1; i < children.length - 2; i = i + 2) {
				System.out.println(children[i].getImage());
			}
			searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
			break;
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
			break;
		}
		case N_SubsetOf: { // { x \in S : e }
			TreeNode[] children = treeNode.heirs();
			String boundedVar = children[1].getImage(); // x
			if (!boundedVariables.contains(boundedVar)) {
				boundedVariables.add(boundedVar);
			}
			searchVarInSyntaxTree(treeNode.heirs()[3]); // S
			searchVarInSyntaxTree(treeNode.heirs()[5]); // e
			break;
		}

		}

		for (int i = 0; i < treeNode.heirs().length; i++) {
			searchVarInSyntaxTree(treeNode.heirs()[i]);
		}
	}
}
