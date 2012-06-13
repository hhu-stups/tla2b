/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import pprint.ExpressionPrinter;
import analysis.TypeChecker;
import analysis.SymbolRenamer;

import exceptions.TLA2BException;
import exceptions.TypeErrorException;
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
	private ArrayList<String> variables;
	private ArrayList<String> noVariables;
	private StringBuilder BExpression;

	public static String translateExpression(String bExpression)
			throws TLA2BException {
		ToolIO.reset();
		ToolIO.setMode(ToolIO.TOOL);
		ExpressionTranslator et = new ExpressionTranslator(bExpression);
		et.start();
		return et.BExpression.toString();
	}

	public ExpressionTranslator(String TLAExpression) {
		this.TLAExpression = TLAExpression;
		this.variables = new ArrayList<String>();
		this.noVariables = new ArrayList<String>();
	}

	public void start() throws TLA2BException {
		String module = "----MODULE Testing----\n" + "Expression == "
				+ TLAExpression + "\n====";

		SpecObj spec = parseModuleWithoutSemanticAnalyse(module);
		evalVariables(spec);
		StringBuilder sb = new StringBuilder();
		sb.append("----MODULE Testing----\n");
		sb.append("EXTENDS Naturals, Integers, Sequences, FiniteSets, TLA2B \n");
		if (variables.size() > 0) {
			sb.append("VARIABLES ");
			for (int i = 0; i < variables.size(); i++) {
				if (i != 0) {
					sb.append(", ");
				}
				sb.append(variables.get(i));
			}
			sb.append("\n");
		}
		sb.append("Expression");
		sb.append(" == ");
		sb.append(TLAExpression);
		sb.append("\n====================");
		// System.out.println(sb);
		BExpression = translate(sb.toString());
	}

	private static StringBuilder translate(String expr) throws TLA2BException {
		ModuleNode moduleNode = parseModule(expr);

		TypeChecker tc = new TypeChecker(moduleNode);
		try {
			tc.start();
		} catch (TLA2BException e) {
			String[] m = ToolIO.getAllMessages();
			String message = m[0] + "\n" + expr + "\n\n****TypeError****\n"
					+ e.getLocalizedMessage();
			//System.out.println(message);
			throw new TypeErrorException(message);
		}

		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode);
		symRenamer.start();

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
		SANY.turnSemanticAnalyseOff();
		SpecObj spec = new SpecObj(module, null);
		try {
			SANY.frontEndMain(spec, module, ToolIO.out);
		} catch (FrontEndException e) {
			throw new exceptions.FrontEndException(e.getLocalizedMessage());
			// Error in Frontend, should never happens
		}

		if (spec.parseErrors.isFailure()) {
			String[] m = ToolIO.getAllMessages();
			String message = m[0] + "\n\n" + module + "\n\n" + m[1];
			throw new exceptions.FrontEndException(message, spec);
		}
		SANY.turnSemanticAnalyseOn();
		return spec;
	}

	public static ModuleNode parseModule(String module)
			throws exceptions.FrontEndException {

		SpecObj spec = new SpecObj(module, null);
		try {
			SANY.frontEndMain(spec, module, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}

		if (spec.parseErrors.isFailure()) {
			String[] m = ToolIO.getAllMessages();
			String message = m[0] + "\n\n" + module + "\n\n" + m[1];
			throw new exceptions.FrontEndException(message, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			String[] m = ToolIO.getAllMessages();
			String message = m[0] + "\n\n" + module + "\n\n"
					+ spec.semanticErrors;
			// System.out.println(message);
			throw new exceptions.FrontEndException(message, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new exceptions.FrontEndException(
					Main.allMessagesToString(ToolIO.getAllMessages()), spec);
		}
		return n;
	}

	/**
	 * @param spec
	 * @return
	 */
	private void evalVariables(SpecObj spec) {
		ParseUnit p = (ParseUnit) spec.parseUnitContext.get("Testing");
		TreeNode n_module = p.getParseTree();
		TreeNode n_body = n_module.heirs()[2];
		TreeNode n_operatorDefintion = n_body.heirs()[0];
		TreeNode expr = n_operatorDefintion.heirs()[2];
		searchVarInSyntaxTree(expr);

		for (int i = 0; i < noVariables.size(); i++) {
			variables.remove(noVariables.get(i));
		}

	}

	private final static Set<String> KEYWORDS = new HashSet<String>();
	static {
		KEYWORDS.add("BOOLEAN");
		KEYWORDS.add("TRUE");
		KEYWORDS.add("FALSE");
		KEYWORDS.add("Nat");
		KEYWORDS.add("Int");
		KEYWORDS.add("Cardinality");
		KEYWORDS.add("IsFiniteSet");
		KEYWORDS.add("Append");
		KEYWORDS.add("Head");
		KEYWORDS.add("Tail");
		KEYWORDS.add("Len");
		KEYWORDS.add("Seq");
		KEYWORDS.add("SubSeq");
		KEYWORDS.add("SelectSeq");
		KEYWORDS.add("MinOfSet");
		KEYWORDS.add("MaxOfSet");
		KEYWORDS.add("SetProduct");
		KEYWORDS.add("SetSummation");
		KEYWORDS.add("PermutedSequences");
		KEYWORDS.add("@");

	}

	/**
	 * 
	 */
	private void searchVarInSyntaxTree(TreeNode treeNode) {
		// System.out.println(treeNode.getKind() + " " + treeNode.getImage());
		switch (treeNode.getKind()) {
		case N_GeneralId: {
			String con = treeNode.heirs()[1].getImage();
			if (!variables.contains(con) && !KEYWORDS.contains(con)) {
				variables.add(con);
			}
			break;
		}
		case N_IdentLHS: { // left side of a definition
			TreeNode[] children = treeNode.heirs();
			noVariables.add(children[0].getImage());
			break;
		}
		case N_IdentDecl: { // parameter of a LET definition
							// e.g. x in LET foo(x) == e
			noVariables.add(treeNode.heirs()[0].getImage());
			break;
		}
		case N_FunctionDefinition: {
			// the first child is the function name
			noVariables.add(treeNode.heirs()[0].getImage());
			break;
		}
		case N_UnboundQuant: {
			TreeNode[] children = treeNode.heirs();
			for (int i = 1; i < children.length - 2; i = i + 2) {
				// System.out.println(children[i].getImage());
			}
			searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
			break;
		}
		case N_QuantBound: {
			TreeNode[] children = treeNode.heirs();
			for (int i = 0; i < children.length - 2; i = i + 2) {
				String boundedVar = children[i].getImage();
				if (!noVariables.contains(boundedVar)) {
					noVariables.add(boundedVar);
				}
			}
			searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
			break;
		}
		case N_SubsetOf: { // { x \in S : e }
			TreeNode[] children = treeNode.heirs();
			String boundedVar = children[1].getImage(); // x
			if (!noVariables.contains(boundedVar)) {
				noVariables.add(boundedVar);
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
