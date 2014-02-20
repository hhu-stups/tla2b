/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.pprint;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;

import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.RecursiveFunktion;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ValueObj;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.EnumType;
import de.tla2b.types.SetType;
import de.tla2b.types.TLAType;

import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.value.SetEnumValue;

public class BMachinePrinter extends AbstractExpressionPrinter implements
		TranslationGlobals {
	private ModuleNode module;
	private ArrayList<OpDeclNode> bConstants;
	private ArrayList<ExprNode> inits;
	private ArrayList<BOperation> bOperations;
	private ArrayList<OpDefNode> invariants;
	private ArrayList<LetInNode> globalLets;
	private ArrayList<String> setEnumeration;
	private ArrayList<String> definitionMacro;
	private Hashtable<OpDeclNode, ValueObj> constantAssignments;
	private ArrayList<OpDefNode> operatorModelvalues;
	private Set<OpDefNode> bDefinitions;
	// set of OpDefNodes which are called in the specification
	private Hashtable<OpDefNode, FormalParamNode[]> letParams;

	private ArrayList<RecursiveFunktion> recursiveFunktions;
	private ArrayList<LetInNode> tempLetInNodes = new ArrayList<LetInNode>();

	/**
	 * @param moduleNode
	 * @param conEval
	 * @param specAnalyser
	 */
	public BMachinePrinter(ModuleNode moduleNode, ConfigfileEvaluator conEval,
			SpecAnalyser specAnalyser) {
		this.module = moduleNode;

		if (conEval == null) {
			bConstants = new ArrayList<OpDeclNode>();
			for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
				bConstants.add(moduleNode.getConstantDecls()[i]);
			}
		} else {
			this.bConstants = conEval.getbConstantList();
			this.invariants = conEval.getInvariants();
			this.setEnumeration = conEval.getEnumerationSet();
			this.constantAssignments = conEval.getConstantAssignments();
			this.operatorModelvalues = conEval.getOperatorModelvalues();
		}

		this.inits = specAnalyser.getInits();
		this.bOperations = specAnalyser.getBOperations();
		this.globalLets = specAnalyser.getGlobalLets();
		this.definitionMacro = specAnalyser.getDefinitionMacros();
		this.bDefinitions = specAnalyser.getBDefinitions();
		this.letParams = specAnalyser.getLetParams();
		this.recursiveFunktions = specAnalyser.getRecursiveFunctions();
	}

	public StringBuilder start() {
		StringBuilder out = new StringBuilder();
		out.append("MACHINE " + module.getName().toString() + "\n");

		out.append(evalEnumeratedSets());

		// Constants and Properties
		out.append(evalConsDecl());
		out.append(evalPropertyStatements());
		tempLetInNodes.clear();
		StringBuilder operations = evalOperations();
		globalLets.addAll(tempLetInNodes);
		tempLetInNodes.clear();

		out.append(evalDefinitions());

		out.append(evalVariables());

		out.append(evalInvariants());

		out.append(evalInit());

		out.append(operations);
		out.append("END");
		return out;
	}

	/**
	 * @return
	 */
	private StringBuilder evalEnumeratedSets() {
		StringBuilder out = new StringBuilder();

		if (setEnumeration == null || setEnumeration.size() == 0)
			return out;

		out.append("SETS\n ");

		ArrayList<EnumType> printed = new ArrayList<EnumType>();
		int counter = 1;

		OpDeclNode[] cons = module.getConstantDecls();
		boolean first = true;
		for (int i = 0; i < cons.length; i++) {
			TLAType type = (TLAType) cons[i].getToolObject(TYPE_ID);
			EnumType e = null;
			if (type instanceof SetType) {
				if (((SetType) type).getSubType() instanceof EnumType) {
					e = (EnumType) ((SetType) type).getSubType();
				} else
					continue;

			} else if ((type instanceof EnumType)) {
				e = (EnumType) type;
			} else
				continue;

			if (!printed.contains(e)) {
				e.id = counter;
				if (!first) {
					out.append("; ");
				}
				out.append("ENUM" + counter + " = {");
				Iterator<String> it2 = e.modelvalues.iterator();
				while (it2.hasNext()) {
					out.append(it2.next());
					if (it2.hasNext()) {
						out.append(", ");
					}
				}
				if (e.hasNoVal()) {
					out.append(", noVal" + counter);
				}
				out.append("}");
				printed.add(e);
				counter++;
				first = false;
			}
		}

		if (operatorModelvalues != null && operatorModelvalues.size() > 0) {
			for (int i = 0; i < operatorModelvalues.size(); i++) {
				OpDefNode def = operatorModelvalues.get(i);
				TLAType type = (TLAType) def.getToolObject(TYPE_ID);
				EnumType e = null;
				if (type instanceof SetType) {
					if (((SetType) type).getSubType() instanceof EnumType) {
						e = (EnumType) ((SetType) type).getSubType();
					} else
						continue;

				} else if ((type instanceof EnumType)) {
					e = (EnumType) type;
				} else
					continue;

				if (!printed.contains(e)) {
					e.id = counter;
					if (!first) {
						out.append("; ");
					}
					out.append("ENUM" + counter + " = {");
					Iterator<String> it2 = e.modelvalues.iterator();
					while (it2.hasNext()) {
						out.append(it2.next());
						if (it2.hasNext()) {
							out.append(", ");
						}
					}
					if (e.hasNoVal()) {
						out.append(", noVal" + counter);
					}
					out.append("}");
					printed.add(e);
					counter++;
					first = false;
				}

			}

		}

		out.append("\n");
		return out;
	}

	private StringBuilder evalInvariants() {
		StringBuilder out = new StringBuilder();
		OpDeclNode[] vars = module.getVariableDecls();
		if (vars.length > 0) {
			out.append("INVARIANT\n ");
			for (int i = 0; i < vars.length; i++) {
				TLAType varType = (TLAType) vars[i].getToolObject(TYPE_ID);
				out.append(getPrintName(vars[i]) + " : " + varType + "\n");
				if (i != vars.length - 1)
					out.append(" & ");
			}
			if (invariants != null) {
				for (int i = 0; i < invariants.size(); i++) {
					out.append(" & " + invariants.get(i).getName().toString()
							+ "\n");
				}
			}
		}
		return out;
	}

	private StringBuilder evalInit() {
		StringBuilder out = new StringBuilder();
		OpDeclNode[] vars = module.getVariableDecls();
		if (vars.length == 0)
			return out;
		out.append("INITIALISATION\n ");
		for (int i = 0; i < vars.length; i++) {
			out.append(getPrintName(vars[i]));
			if (i < vars.length - 1)
				out.append(", ");
		}
		out.append(":(");
		for (int i = 0; i < inits.size(); i++) {
			if (i != 0) {
				out.append(" & ");
			}
			out.append(visitExprNode(inits.get(i), new DContext(), PREDICATE).out);
		}
		out.append(")\n");
		return out;
	}

	private StringBuilder evalOperations() {
		StringBuilder out = new StringBuilder();
		if (bOperations == null)
			return out;

		out.append("OPERATIONS\n");
		for (int i = 0; i < bOperations.size(); i++) {
			BOperation op = bOperations.get(i);
			String defName = op.getName();

			DContext d = new DContext("\t");
			out.append(" " + defName.replace('!', '_') + "_Op");
			if (op.getOpParams().size() > 0) {
				out.append("(");
				for (int j = 0; j < op.getOpParams().size(); j++) {
					if (j != 0)
						out.append(", ");
					out.append(op.getOpParams().get(j));
				}
				out.append(")");
			}
			out.append(" = ");
			out.append("ANY ");
			OpDeclNode[] vars = module.getVariableDecls();
			boolean first = true;
			for (int j = 0; j < vars.length; j++) {
				String varName = vars[j].getName().toString();
				if (op.getUnchangedVariables().contains(varName))
					continue;
				if (!first) {
					out.append(", ");
				}
				out.append(varName + "_n");
				first = false;
			}
			out.append("\n\tWHERE ");
			if (op.getOpParams().size() > 0) {
				for (int j = 0; j < op.getExistQuans().size(); j++) {
					OpApplNode o = op.getExistQuans().get(j);
					out.append(visitBounded(o, d));
					out.append(" & ");
				}
				out.append("\n\t ");
			}
			for (int j = 0; j < vars.length; j++) {
				String varName = vars[j].getName().toString();
				if (op.getUnchangedVariables().contains(varName))
					continue;
				out.append(varName + "_n : " + vars[j].getToolObject(TYPE_ID));
				out.append(" & ");
			}
			out.append(visitExprOrOpArgNode(op.getNode(), d, PREDICATE).out);

			out.append("\n\tTHEN ");

			boolean first2 = true;
			for (int j = 0; j < vars.length; j++) {
				String varName = vars[j].getName().toString();
				if (op.getUnchangedVariables().contains(varName))
					continue;
				if (!first2) {
					out.append(", ");
				}
				out.append(varName);
				first2 = false;
			}

			out.append(" := ");

			boolean first3 = true;
			for (int j = 0; j < vars.length; j++) {
				String varName = vars[j].getName().toString();
				if (op.getUnchangedVariables().contains(varName))
					continue;
				if (!first3) {
					out.append(", ");
				}
				out.append(varName + "_n");
				first3 = false;
			}
			out.append(" END");
			if (i != bOperations.size() - 1) {
				out.append(";\n\n");
			}
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalVariables() {
		StringBuilder out = new StringBuilder();
		OpDeclNode[] vars = module.getVariableDecls();
		if (vars.length > 0) {
			out.append("VARIABLES\n ");
			for (int i = 0; i < vars.length; i++) {
				String[] comments = vars[i].getPreComments();
				if (comments.length > 0) {
					String pragma = comments[comments.length - 1];
					if (pragma.startsWith("(*@")) {
						pragma = pragma.replace('(', '/').replace(')', '/');
						out.append(pragma).append(" ");
					}

				}
				out.append(getPrintName(vars[i]));
				if (i != vars.length - 1)
					out.append(",\n ");
			}
			out.append("\n");
		}
		return out;
	}

	private StringBuilder evalDefinitions() {
		StringBuilder out = new StringBuilder();
		ArrayList<OpDefNode> bDefs = new ArrayList<OpDefNode>();
		for (int i = 0; i < module.getOpDefs().length; i++) {
			OpDefNode def = module.getOpDefs()[i];
			if (bDefinitions.contains(def))
				bDefs.add(def);
		}

		if (bDefs.size() + globalLets.size() + definitionMacro.size() == 0)
			return out;
		out.append("DEFINITIONS\n");
		for (int i = 0; i < definitionMacro.size(); i++) {
			out.append(definitionMacro.get(i));
			if (i != definitionMacro.size() - 1
					|| bDefs.size() + globalLets.size() > 0) {
				out.append(";\n");
			}
		}

		for (int i = 0; i < bDefs.size(); i++) {
			out.append(visitOpDefNode(bDefs.get(i)));
			if (!(i == bDefs.size() - 1 && globalLets.size() == 0))
				out.append(";\n\n");
		}

		for (int i = 0; i < globalLets.size(); i++) {
			LetInNode letInNode = globalLets.get(i);
			for (int j = 0; j < letInNode.getLets().length; j++) {
				out.append(evalLet(letInNode.getLets()[j]));
				if (i != letInNode.getLets().length - 1)
					out.append(";\n");
			}
			if (i != globalLets.size() - 1)
				out.append(";\n");
		}
		out.append("\n");
		return out;
	}

	/**
	 * @param letDef
	 * @return
	 */
	private StringBuilder evalLet(OpDefNode letDef) {
		StringBuilder out = new StringBuilder();
		String defName = getPrintName(letDef);
		out.append(" " + defName);
		FormalParamNode[] shiftParams = letParams.get(letDef);
		if (shiftParams == null)
			shiftParams = new FormalParamNode[0];
		if (letDef.getParams().length + shiftParams.length > 0) {
			out.append("(");
			for (int i = 0; i < letDef.getParams().length; i++) {
				if (i != 0)
					out.append(",");
				out.append(letDef.getParams()[i].getName().toString());
			}
			for (int i = 0; i < shiftParams.length; i++) {
				if (letDef.getParams().length > 0 || i != 0)
					out.append(", ");
				out.append(shiftParams[i].getName().toString());

			}
			out.append(")");
		}
		out.append(" == ");
		DContext d = new DContext("\t");
		out.append(visitExprNode(letDef.getBody(), d, VALUEORPREDICATE).out);
		return out;

	}

	/**
	 * @param def
	 */
	private StringBuilder visitOpDefNode(OpDefNode def) {
		StringBuilder out = new StringBuilder();
		// ConstantObj conObj = (ConstantObj) def.getSource().getToolObject(
		// CONSTANT_OBJECT);
		// if (conObj != null) {
		// System.out.println("hier");
		// // config substitution
		// // out.append(" " + defName.replace('!', '_'));
		// String defName = getPrintName(def);
		// String defValue = conObj.getValue().toString();
		// if(defName.equals(defName.equals(defValue)))
		// return out;
		// out.append(" " + defName);
		// out.append(" == " + defValue);
		// return out;
		// }

		DContext d = new DContext("\t");
		tempLetInNodes.clear();
		StringBuilder body = visitExprNode(def.getBody(), d, VALUEORPREDICATE).out;

		for (int i = 0; i < tempLetInNodes.size(); i++) {
			LetInNode letInNode = tempLetInNodes.get(i);
			for (int j = 0; j < letInNode.getLets().length; j++) {
				out.append(evalLet(letInNode.getLets()[j]));
				out.append(";\n");
			}

		}
		tempLetInNodes.clear();

		out.append(" " + getPrintName(def));
		FormalParamNode[] params = def.getParams();
		if (params.length > 0) {
			out.append("(");
			for (int i = 0; i < params.length; i++) {
				if (i != 0)
					out.append(", ");
				out.append(getPrintName(params[i]));
			}
			out.append(")");
		}
		out.append(" == ");
		out.append(body);
		return out;
	}

	private StringBuilder evalConsDecl() {
		StringBuilder out = new StringBuilder();
		if (bConstants.size() + recursiveFunktions.size() == 0)
			return out;
		out.append("ABSTRACT_CONSTANTS\n");
		// out.append("CONSTANTS ");
		for (int i = 0; i < bConstants.size(); i++) {
			String[] comments = bConstants.get(i).getPreComments();
			if (comments.length > 0) {
				String pragma = comments[comments.length - 1];
				if (pragma.startsWith("(*@")) {
					pragma = pragma.replace('(', '/').replace(')', '/');
					out.append(pragma).append(" ");
				}

			}
			out.append(getPrintName(bConstants.get(i)));
			if (i < bConstants.size() - 1 || recursiveFunktions.size() > 0)
				out.append(",\n ");
		}
		for (int i = 0; i < recursiveFunktions.size(); i++) {
			out.append(getPrintName(recursiveFunktions.get(i).getOpDefNode()));
			if (i < recursiveFunktions.size() - 1)
				out.append(", ");
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalPropertyStatements() {
		StringBuilder out = new StringBuilder();
		if (bConstants.size() == 0 && module.getAssumptions().length == 0) {
			return out;
		}
		out.append("PROPERTIES\n ");
		boolean notFirst = false;
		for (int i = 0; i < bConstants.size(); i++) {
			OpDeclNode con = bConstants.get(i);
			if (notFirst) {
				out.append(" & ");
			}
			if (constantAssignments != null
					&& constantAssignments.containsKey(con)) {
				ValueObj v = constantAssignments.get(con);
				TLAType t = v.getType();
				boolean isEnum = false;
				if (t instanceof SetType) {
					TLAType sub = ((SetType) t).getSubType();
					if (sub instanceof EnumType) {
						EnumType en = (EnumType) sub;
						SetEnumValue set = (SetEnumValue) v.getValue();
						if (set.elems.size() == en.modelvalues.size()) {
							isEnum = true;
						}
					}
				}
				if (isEnum) {
					out.append(String.format("%s = %s\n", getPrintName(con),
							((SetType) t).getSubType()));
				} else {
					out.append(String.format("%s = %s\n", getPrintName(con), v
							.getValue().toString()));
				}

			} else {
				out.append(String.format("%s : %s\n", getPrintName(con),
						con.getToolObject(TYPE_ID)));
			}

			notFirst = true;
		}
		out.append(evalAssumptions());
		return out;
	}

	private StringBuilder evalAssumptions() {
		AssumeNode[] assumes = module.getAssumptions();
		StringBuilder out = new StringBuilder();
		if (assumes.length == 0)
			return out;
		if (bConstants.size() > 0) {
			out.append(" & ");
		}
		tempLetInNodes.clear();
		for (int i = 0; i < assumes.length; i++) {
			if (i != 0) {
				out.append(" & ");
			}
			out.append(visitAssumeNode(assumes[i]));
			out.append("\n");
		}
		globalLets.addAll(tempLetInNodes);
		tempLetInNodes.clear();

		if (recursiveFunktions.size() == 0)
			return out;
		if (bConstants.size() + assumes.length > 0) {
			out.append(" & ");
		}
		for (int i = 0; i < recursiveFunktions.size(); i++) {
			if (i != 0) {
				out.append(" & ");
			}
			out.append(visitRecursiveFunction(recursiveFunktions.get(i)));
			out.append("\n");
		}

		return out;
	}

	/**
	 * @param recursiveFunktion
	 * @return
	 */
	private StringBuilder visitRecursiveFunction(RecursiveFunktion rf) {
		StringBuilder out = new StringBuilder();
		OpApplNode o = rf.getRF();
		OpApplNode ifThenElse = rf.getIfThenElse();
		out.append(getPrintName(rf.getOpDefNode()));
		out.append(" = ");

		DContext d = new DContext();

		FormalParamNode[][] vars = o.getBdedQuantSymbolLists();
		StringBuilder pre = new StringBuilder();
		for (int i = 0; i < vars.length; i++) {
			for (int j = 0; j < vars[i].length; j++) {
				pre.append(vars[i][j].getName());
				if (j < vars[i].length - 1) {
					pre.append(",");
				}
			}
			if (i < vars.length - 1) {
				pre.append(",");
			}
		}
		StringBuilder bound = visitBounded(o, d);

		ExprReturn iif = visitExprOrOpArgNode(ifThenElse.getArgs()[0], d,
				PREDICATE);
		ExprReturn then = visitExprOrOpArgNode(ifThenElse.getArgs()[1], d,
				VALUE);
		ExprReturn eelse = visitExprOrOpArgNode(ifThenElse.getArgs()[2], d,
				VALUE);
		String res = String.format(
				"%%%s.(%s & %s | %s) \\/ %%%s.(%s & not(%s) | %s)", pre, bound,
				iif.out, then.out, pre, bound, iif.out, eelse.out);
		out.append(res);
		return out;
	}

	private StringBuilder visitAssumeNode(AssumeNode n) {
		// there are named or unnamend assumptions
		StringBuilder out = new StringBuilder();
		DContext d = new DContext();
		out.append(visitExprNode(n.getAssume(), d, PREDICATE).out);

		return out;
	}

	@Override
	protected ExprReturn visitLetInNode(LetInNode l, DContext d, int expected) {
		tempLetInNodes.add(l);
		return visitExprNode(l.getBody(), d, VALUEORPREDICATE);
	}

	@Override
	protected ExprReturn visitUserdefinedOp(OpApplNode n, DContext d,
			int expected) {
		StringBuilder out = new StringBuilder();
		OpDefNode def = (OpDefNode) n.getOperator();
		// Operator is a B built-in operator
		if (BBuiltInOPs.contains(def.getName())
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
			return evalBBuiltIns(n, d, expected);
		}

		out.append(getPrintName(def));

		FormalParamNode[] shiftedParams = letParams.get(def);
		if (n.getArgs().length > 0
				|| (shiftedParams != null && shiftedParams.length > 0)) {
			out.append("(");
			for (int i = 0; i < n.getArgs().length; i++) {
				out.append(visitExprOrOpArgNode(n.getArgs()[i], d, VALUE).out);
				if (i < n.getArgs().length - 1) {
					out.append(", ");
				}
			}
			if (shiftedParams != null) {
				for (int i = 0; i < shiftedParams.length; i++) {
					if (n.getArgs().length > 0 || i != 0)
						out.append(", ");
					out.append(shiftedParams[i].getName().toString());

				}
			}
			out.append(")");

		}
		TLAType defType = (TLAType) n.getToolObject(TYPE_ID);
		if (defType != null && defType.getKind() == BOOL) {
			return makeBoolValue(out, expected, P_max);
		}
		return new ExprReturn(out);
	}

}
