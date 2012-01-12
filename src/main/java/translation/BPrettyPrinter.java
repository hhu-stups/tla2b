/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tlc2.tool.BuiltInOPs;
import tlc2.value.SetEnumValue;
import types.BType;
import types.EnumType;
import types.IType;
import types.PowerSetType;
import types.StructType;
import util.StandardModules;
import util.UniqueString;

public class BPrettyPrinter extends BuiltInOPs implements ASTConstants, IType,
		BBuildIns, Priorities, TranslationGlobals {
	private ModuleNode module;
	private ModuleContext moduleContext;
	private int toolId = 5;
	private int substitutionId = 10;

	private final int NOBOOL = 0;
	private final int VALUE = 1;
	private final int PREDICATE = 2;
	private final int VALUEORPREDICATE = 3;

	public BPrettyPrinter(ModuleNode n, ModuleContext c) {
		module = n;
		moduleContext = c;
	}

	public StringBuilder start() {
		StringBuilder out = new StringBuilder();
		out.append("MACHINE " + module.getName().toString() + "\n");

		out.append(evalEnumeratedSets());

		// Constants and Properties
		out.append(evalConsDecl());
		out.append(evalPropertyStatements());

		StringBuilder operations = evalOperations();

		out.append(evalDefinition());

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
		if (moduleContext.getEnum()== null)
			return out;
		out.append("SETS\n ");
		
		ArrayList<EnumType> printed = new ArrayList<EnumType>();
		int counter = 1;
		Iterator<ConstantObj> it =moduleContext.conObjs.values().iterator();
		boolean first = true;
		while (it.hasNext()) {
			BType type = it.next().getType();
			EnumType e = null;
			if(type instanceof PowerSetType){
				if(((PowerSetType) type).getSubType() instanceof EnumType){
					e = (EnumType) ((PowerSetType) type).getSubType();
				}else continue;
					
			}else if((type instanceof EnumType)){
				e = (EnumType) type;
			}else continue;
			
			if(!printed.contains(e)){
				e.id = counter;
				if(!first){
					out.append("; ");					
				}
				out.append("ENUM"+counter+" = {");
				Iterator<String> it2 = e.modelvalues.iterator();
				while (it2.hasNext()) {
					out.append(it2.next());
					if(it2.hasNext()){
						out.append(", ");
					}
				}
				out.append("}");
				printed.add(e);
				counter++;
				first = false;
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
				BType varType = (BType) vars[i].getToolObject(toolId);
				out.append(vars[i].getName().toString() + " : " + varType
						+ "\n");
				if (i != vars.length - 1)
					out.append(" & ");
			}
			for (int i = 0; i < moduleContext.getInvariants().size(); i++) {
				out.append(" & " + moduleContext.getInvariants().get(i) + "\n");
			}
		}
		return out;
	}

	private StringBuilder evalInit() {
		StringBuilder out = new StringBuilder();
		if (module.getVariableDecls().length == 0)
			return out;
		out.append("INITIALISATION\n ");
		for (int i = 0; i < module.getVariableDecls().length; i++) {
			out.append(module.getVariableDecls()[i].getName());
			if (i < module.getVariableDecls().length - 1)
				out.append(", ");
		}
		out.append(":(");
		for (int i = 0; i < moduleContext.inits.size(); i++) {
			if (i != 0) {
				out.append(" & ");
			}
			BInit bInit = moduleContext.inits.get(i);
			out.append(visitExprNode(bInit.getNode(),
					new DContext(bInit.getPrefix()), PREDICATE).out);
		}
		out.append(")\n");
		return out;
	}

	private StringBuilder evalOperations() {
		StringBuilder out = new StringBuilder();
		ArrayList<BOperation> ops = moduleContext.bOperations;
		if (ops.size() == 0)
			return out;

		out.append("OPERATIONS\n");
		for (int i = 0; i < ops.size(); i++) {
			BOperation op = ops.get(i);
			String defName = op.getName();

			String prefix = defName.substring(0, defName.lastIndexOf('!') + 1);
			DContext d = new DContext(prefix, "\t");
			d.localDefinitions = new LinkedHashMap<String, LetDef>(
					op.getLocalDefintions());

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
			out.append(visitExprOrOpArgNode(op.getNode(), d, PREDICATE).out);

			for (Iterator<LetDef> itr = d.localDefinitions.values().iterator(); itr
					.hasNext();) {
				LetDef letDef = itr.next();
				if (!op.getLocalDefintions().containsValue(letDef)) {
					moduleContext.globalLets.add(letDef);
				}
			}

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
			if (i != ops.size() - 1) {
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
			out.append("VARIABLES ");
			for (int i = 0; i < vars.length; i++) {
				String name = vars[i].getName().toString();
				out.append(name);
				if (i != vars.length - 1)
					out.append(", ");
			}
			out.append("\n");
		}
		return out;
	}

	private StringBuilder evalDefinition() {
		StringBuilder out = new StringBuilder();
		boolean first = true;
		OpDefNode[] opDefs = module.getOpDefs();
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
			// Definition in this module
			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
					.getName().toString())
					|| StandardModules.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}
			Boolean usedDefintion = (Boolean) def
					.getToolObject(PRINT_DEFINITION);
			if (usedDefintion != null && usedDefintion) {
				ConstantObj conObj = (ConstantObj) def
						.getToolObject(CONSTANT_OBJECT);
				if (conObj != null) {
					if (def.getName().toString().equals(conObj.getValue())) {
						// defname equals modelvalues
						continue;
					}
				}
				if (first) {
					out.append("DEFINITIONS\n");
					first = false;
				}
				out.append(visitOpDefNode(def));
			}
		}

		if (moduleContext.globalLets.size() > 0) {
			if (first) {
				out.append("DEFINITIONS\n");
				first = false;
			}
			for (int i = 0; i < moduleContext.globalLets.size(); i++) {
				out.append(evalLet(moduleContext.globalLets.get(i)));
			}
		}
		return out;
	}

	/**
	 * @param letDef
	 * @return
	 */
	private StringBuilder evalLet(LetDef letDef) {
		StringBuilder out = new StringBuilder();
		String defName = letDef.getName();
		defName = defName.replace('!', '_');
		out.append(" " + defName);
		OpDefNode n = letDef.getNode();
		ArrayList<String> params = letDef.getParameters();
		if (n.getParams().length > 0 || params.size() > 0) {
			out.append("(");
			for (int i = 0; i < n.getParams().length; i++) {
				if (i != 0)
					out.append(",");
				out.append(n.getParams()[i].getName().toString());
			}
			for (int i = 0; i < params.size(); i++) {
				if (n.getParams().length > 0 || i != 0)
					out.append(", ");
				out.append(params.get(i));

			}
			out.append(")");
		}
		out.append(" == ");
		DContext d = new DContext("", "\t");
		d.localDefinitions = letDef.getlocalDefinition();
		out.append(visitExprNode(letDef.getNode().getBody(), d,
				VALUEORPREDICATE).out);
		out.append(";\n");
		return out;

	}

	/**
	 * @param def
	 */
	private StringBuilder visitOpDefNode(OpDefNode def) {
		StringBuilder out = new StringBuilder();
		String defName = def.getName().toString();
		ConstantObj conObj = (ConstantObj) def.getToolObject(CONSTANT_OBJECT);
		if (conObj != null) {
			// config substitution
			out.append(" " + defName.replace('!', '_'));
			out.append(" == " + conObj.getValue() + ";\n\n");
			return out;
		}

		String prefix = defName.substring(0, defName.lastIndexOf('!') + 1);
		DContext d = new DContext(prefix, "\t");
		StringBuilder body = visitExprNode(def.getBody(), d, VALUEORPREDICATE).out;
		// first print the local defintions
		for (Iterator<LetDef> itr = d.localDefinitions.values().iterator(); itr
				.hasNext();) {
			out.append(evalLet(itr.next()));
		}

		defName = defName.replace('!', '_');
		out.append(" " + defName);
		FormalParamNode[] params = def.getParams();
		if (params.length > 0) {
			out.append("(");
			for (int i = 0; i < params.length; i++) {
				if (i != 0)
					out.append(",");
				out.append(params[i].getName().toString());
			}
			out.append(")");
		}
		out.append(" == ");
		out.append(body);
		out.append(";\n\n");
		return out;
	}

	private StringBuilder evalConsDecl() {
		StringBuilder out = new StringBuilder();
		ArrayList<String> bCons = moduleContext.getBConstants();
		OpDeclNode[] cons = module.getConstantDecls();
		if (bCons.size() == 0)
			return out;
		out.append("CONSTANTS ");
		boolean flag = false;
		for (int i = 0; i < cons.length; i++) {

			String con = cons[i].getName().toString();
			if (bCons.contains(con)) {
				if (flag) {
					out.append(", ");
				}
				out.append(con);
				flag = true;
			}
		}
		out.append("\n");
		return out;
	}

	private StringBuilder evalPropertyStatements() {
		StringBuilder out = new StringBuilder();
		if (moduleContext.getBConstants().size() == 0
				&& module.getAssumptions().length == 0) {
			return out;
		}
		OpDeclNode[] cons = module.getConstantDecls();
		out.append("PROPERTIES\n ");
		boolean flag = false;
		for (int i = 0; i < cons.length; i++) {
			String conName = cons[i].getName().toString();
			if (moduleContext.getBConstants().contains(conName)) {
				if (flag) {
					out.append(" & ");
				}
				if (moduleContext.conObjs != null
						&& moduleContext.conObjs.get(conName) != null) {
					ConstantObj c = moduleContext.conObjs.get(conName);
					BType t = c.getType();
					boolean isEnum = false;
					if (t instanceof PowerSetType){
						BType sub = ((PowerSetType)t).getSubType(); 
						if (sub instanceof EnumType){
							EnumType en = (EnumType)sub;
							SetEnumValue set = (SetEnumValue) c.getValue();
							if (set.elems.size()==en.modelvalues.size()){
								isEnum = true;
							}
							
						}
					}
					if(isEnum){
						out.append(String.format("%s = %s\n", conName, ((PowerSetType)t).getSubType()));
					}else{
						out.append(String.format("%s = %s\n", conName, c.getValue().toString()));
					}

				} else {
					out.append(String.format("%s : %s\n", conName,
							cons[i].getToolObject(toolId)));
				}

				flag = true;
			}
		}
		out.append(evalAssumptions());
		out.append(evalOverrides());
		return out;
	}

	private StringBuilder evalAssumptions() {
		AssumeNode[] assumes = module.getAssumptions();
		StringBuilder out = new StringBuilder();
		if (assumes.length == 0)
			return out;
		if (moduleContext.getBConstants().size() > 0) {
			out.append(" & ");
		}
		for (int i = 0; i < assumes.length; i++) {
			if (i != 0) {
				out.append(" & ");
			}
			out.append(visitAssumeNode(assumes[i]));
			out.append("\n");
		}
		return out;
	}

	private StringBuilder evalOverrides() {
		StringBuilder out = new StringBuilder();
		if (moduleContext.getOverrides() == null) {
			return out;
		}
		Hashtable<String, String> over = moduleContext.getOverrides();
		Enumeration<String> keys = over.keys();
		while (keys.hasMoreElements()) {
			out.append(" & ");
			String key = keys.nextElement();
			out.append(key + " = " + over.get(key) + "\n");
		}
		return out;
	}

	private StringBuilder visitAssumeNode(AssumeNode n) {
		// there are named or unnamend assumptions
		StringBuilder out = new StringBuilder();
		DContext d = new DContext("");
		out.append(visitExprNode(n.getAssume(), d, PREDICATE).out);

		for (Iterator<LetDef> itr = d.localDefinitions.values().iterator(); itr
				.hasNext();) {
			moduleContext.globalLets.add(itr.next());
		}
		return out;
	}

	private ExprReturn visitExprOrOpArgNode(ExprOrOpArgNode n, DContext d,
			int expected) {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, d, expected);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	private ExprReturn visitExprNode(ExprNode n, DContext d, int expected) {
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

		case SubstInKind: {
			SubstInNode substInNode = (SubstInNode) n;

			Subst[] subs = substInNode.getSubsts();
			for (int i = 0; i < subs.length; i++) {
				OpDeclNode op = subs[i].getOp();
				op.setToolObject(substitutionId, subs[i].getExpr());
			}
			return visitExprNode(substInNode.getBody(), d, expected);
		}

		case LetInKind: {
			LetInNode l = (LetInNode) n;
			for (int i = 0; i < l.getLets().length; i++) {
				OpDefNode def = l.getLets()[i];
				@SuppressWarnings("unchecked")
				ArrayList<String> params = (ArrayList<String>) def
						.getToolObject(moduleContext.letParamsId);
				String letName = moduleContext.createName(def.getName()
						.toString());
				LetDef letDef = new LetDef(letName, def, params,
						d.localDefinitions);
				d.localDefinitions.put(def.getName().toString(), letDef);
			}
			return visitExprNode(l.getBody(), d, VALUEORPREDICATE);

		}
		case AtNodeKind: { // @
			AtNode at = (AtNode) n;
			String base = visitExprNode(at.getAtBase(), d, NOBOOL).out
					.toString();
			BType t = (BType) at.getExceptRef().getToolObject(toolId);
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

		}
		throw new RuntimeException(n.toString(2));
	}

	private ExprReturn visitOpApplNode(OpApplNode n, DContext d, int expected) {
		StringBuilder out = new StringBuilder();
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			OpDeclNode con = (OpDeclNode) n.getOperator();
			ExprOrOpArgNode substExpr = (ExprOrOpArgNode) con
					.getToolObject(substitutionId);
			String overrideName = (String) con
					.getToolObject(OVERRIDE_SUBSTITUTION_ID);
			if (substExpr != null) {
				String prefix = d.getPrefix();
				if (prefix.length() > 0) {
					prefix = prefix.substring(0, prefix.length() - 1);
					int last_ = prefix.lastIndexOf('!');
					if (last_ != -1) {
						prefix = prefix.substring(0,
								prefix.lastIndexOf('!') + 1);
					} else {
						prefix = "";
					}
				}
				if (substExpr instanceof OpArgNode) {
					prefix = prefix.replace('!', '_');
					out.append(prefix
							+ ((OpArgNode) substExpr).getName().toString());
				} else {
					out.append(visitExprOrOpArgNode(substExpr, new DContext(
							prefix), VALUE).out);
				}

			} else if (overrideName != null) {
				out.append(overrideName);
			} else {
				String cName = n.getOperator().getName().toString();
				out.append(cName);
			}

			if (n.getArgs().length > 0) {
				out.append("(");
				for (int i = 0; i < n.getArgs().length; i++) {
					if (i != 0) {
						out.append(",");
					}
					out.append(visitExprOrOpArgNode(n.getArgs()[i], d, VALUE).out);
				}
				out.append(")");
			}

			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}
		case VariableDeclKind: {
			ExprOrOpArgNode e = (ExprOrOpArgNode) n.getOperator()
					.getToolObject(substitutionId);
			if (e != null) {
				return visitExprOrOpArgNode(e, new DContext(""), VALUE);
			}
			String vName = n.getOperator().getName().toString();
			out.append(vName);
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}

		case BuiltInKind:
			return evalBuiltInKind(n, d, expected);

		case FormalParamKind: {
			ExprOrOpArgNode e = (ExprOrOpArgNode) n.getOperator()
					.getToolObject(substitutionId);
			if (e != null) {
				return visitExprOrOpArgNode(e, new DContext(""), VALUE);
			}

			String pName = n.getOperator().getName().toString();
			out.append(pName);
			if (expected == PREDICATE) {
				out.append(" = TRUE");
				return new ExprReturn(out, P_equals);
			}
			return new ExprReturn(out);
		}

		case UserDefinedOpKind: {
			// Operator ist ein B-BuiltIn-Operator
			if (BBuiltInOPs.contains(n.getOperator().getName())) {
				return evalBBuiltIns(n, d, expected);
			}

			OpDefNode def = (OpDefNode) n.getOperator();
			String defName = d.getPrefix() + def.getName().toString();

			if (!moduleContext.definitions.containsKey(defName)
					&& !d.localDefinitions
							.containsKey(def.getName().toString())) {
				// definition of module around the inner module calling the
				// defintion
				defName = def.getName().toString();
			}
			// let definition
			if (!moduleContext.definitions.containsKey(defName)) {

				LetDef letDef = d.localDefinitions
						.get(def.getName().toString());
				if (letDef == null) {
					// letDef =
					// moduleContext.lets.get(def.getName().toString());
					System.out.println(def.toString(4));
					throw new RuntimeException("Unkown Defintion: "
							+ def.getName());
				}
				ArrayList<String> params = letDef.getParameters();

				String letName = letDef.getName();
				out.append(letName.replace('!', '_'));

				if (n.getArgs().length > 0 || params.size() > 0) {
					out.append("(");
					for (int i = 0; i < n.getArgs().length; i++) {
						if (i != 0) {
							out.append(", ");
						}
						out.append(visitExprOrOpArgNode(n.getArgs()[i], d,
								VALUE).out);
					}
					for (int i = 0; i < params.size(); i++) {
						if (n.getArgs().length > 0 || i != 0)
							out.append(", ");
						out.append(params.get(i));

					}
					out.append(")");

				}
				BType defType = (BType) n.getToolObject(toolId);
				if (defType.getKind() == BOOL) {
					return makeBoolValue(out, expected, P_max);
				}
				return new ExprReturn(out);
			}

			out.append(defName.replace('!', '_'));
			if (n.getArgs().length > 0) {
				out.append("(");
				for (ExprOrOpArgNode arg : n.getArgs()) {
					out.append(visitExprOrOpArgNode(arg, d, VALUE).out);
					out.append(", ");
				}
				out.delete(out.length() - 2, out.length());
				out.append(")");

			}
			BType defType = (BType) n.getToolObject(toolId);
			if (defType.getKind() == BOOL) {
				return makeBoolValue(out, expected, P_max);
			}
			return new ExprReturn(out);
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
		case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
		{
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

		case OPCODE_fa: // f[1]
		{
			out.append(visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out);
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
			BType t = (BType) n.getToolObject(toolId);
			if (t.getKind() == STRUCT) {
				Hashtable<String, String> temp = new Hashtable<String, String>();
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode s = (StringNode) pair.getChildren()[0]
							.getChildren()[0];
					String fieldName = s.getRep().toString();
					String val = visitExprOrOpArgNode(
							(ExprOrOpArgNode) pair.getChildren()[1], d, VALUE).out
							.toString();
					temp.put(fieldName, val);
				}
				String oldRec = visitExprOrOpArgNode(n.getArgs()[0], d, NOBOOL).out
						.toString();
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
			return evalStructOrRec("struct", n, d);
		}

		case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
			return evalStructOrRec("rec", n, d);
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

			BType t = (BType) n.getToolObject(toolId);

			if (t.getKind() == BOOL) {
				d.indent.append(" ");
				ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d,
						PREDICATE);
				ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d,
						PREDICATE);
				ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d,
						PREDICATE);
				String res = String.format(
						"(%s \n%s => %s) \n\t & (not(%s) \n%s => %s)",
						brackets(iif, P_implies, true), d.indent,
						brackets(then, P_implies, false), iif.out, d.indent,
						brackets(eelse, P_implies, false));
				return makeBoolValue(new StringBuilder(res), expected, P_and);
			} else {
				ExprReturn iif = visitExprOrOpArgNode(n.getArgs()[0], d,
						PREDICATE);
				ExprReturn then = visitExprOrOpArgNode(n.getArgs()[1], d, VALUE);
				ExprReturn eelse = visitExprOrOpArgNode(n.getArgs()[2], d,
						VALUE);
				String res = String
						.format("(%%t_.( t_ = 0 & %s | %s )\\/%%t_.( t_ = 0 & not(%s) | %s ))(0)",
								iif.out, then.out, iif.out, eelse.out);
				return new ExprReturn(res);
			}
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

	private ExprReturn evalBBuiltIns(OpApplNode n, DContext d, int expected) {

		UniqueString name = n.getOperator().getName();
		StringBuilder out = new StringBuilder();

		switch (BBuiltInOPs.getOpcode(name)) {

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
			String res = String
					.format("#seq_.(seq_ : seq(%s) & !s.(s : %s => #n.(n : 1 .. size(seq_) & seq_(n) = s)))",
							exprr.out, exprr.out);
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

	private StringBuilder visitBounded(OpApplNode n, DContext d) {
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

	private StringBuilder evalOpMoreArgs(OpApplNode n, String operator,
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

	private ExprReturn makeBoolValue(StringBuilder out, int expected,
			int priority) {
		StringBuilder res = new StringBuilder();
		if (expected == VALUE) {
			res.append("bool(" + out + ")");
			return new ExprReturn(res);
		} else {
			return new ExprReturn(out, priority);
		}
	}

	private StringBuilder brackets(ExprReturn r, int p, boolean left) {
		StringBuilder res = new StringBuilder();
		if ((left && r.getPriority() < p) || (!left && r.getPriority() <= p)) {
			res.append("(");
			res.append(r.getOut());
			res.append(")");
		} else
			res.append(r.getOut());
		return res;
	}

}
