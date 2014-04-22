package de.tla2b.analysis;

import java.util.HashMap;

import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.BuiltInOPs;

public class PredicateVsExpression extends BuiltInOPs implements ASTConstants,
		BBuildIns, TranslationGlobals {

	private final HashMap<OpDefNode, DefinitionType> definitionsTypeMap;

	public enum DefinitionType {
		PREDICATE, EXPRESSION
	}

	public DefinitionType getDefinitionType(OpDefNode def) {
		return definitionsTypeMap.get(def);
	}

	public PredicateVsExpression(ModuleNode moduleNode) {
		this.definitionsTypeMap = new HashMap<OpDefNode, PredicateVsExpression.DefinitionType>();
		OpDefNode[] defs = moduleNode.getOpDefs();

		for (int i = 0; i < defs.length; i++) {
			OpDefNode def = defs[i];
			DefinitionType type = visitSemanticNode(defs[i].getBody());
			definitionsTypeMap.put(def, type);
		}

	}

	private DefinitionType visitSemanticNode(SemanticNode s) {
		switch (s.getKind()) {
		case OpApplKind: {
			return visitOppApplNode((OpApplNode) s);
		}

		case LetInKind: {
			LetInNode letInNode = (LetInNode) s;
			return visitSemanticNode(letInNode.getBody());
		}

		}

		return DefinitionType.EXPRESSION;
	}

	private DefinitionType visitOppApplNode(OpApplNode s) {
		OpApplNode opApplNode = (OpApplNode) s;
		int kind = opApplNode.getOperator().getKind();

		if (kind == BuiltInKind) {
			switch (getOpCode(opApplNode.getOperator().getName())) {
			case OPCODE_eq: // =
			case OPCODE_noteq: // /=
			case OPCODE_cl: // $ConjList
			case OPCODE_land: // \land
			case OPCODE_dl: // $DisjList
			case OPCODE_lor: // \/
			case OPCODE_equiv: // \equiv
			case OPCODE_implies: // =>
			case OPCODE_lnot: // \lnot
			case OPCODE_be: // \E x \in S : P
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_in: // \in
			case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
			case OPCODE_unchanged: {
				return DefinitionType.PREDICATE;
			}

			case OPCODE_ite: // IF THEN ELSE
			{
				return visitSemanticNode(opApplNode.getArgs()[1]);
			}

			case OPCODE_case: // CASE p1 -> e1 [] p2 -> e2
			{
				OpApplNode pair = (OpApplNode) opApplNode.getArgs()[0];
				return visitSemanticNode(pair.getArgs()[1]);
			}

			default: {
				return DefinitionType.EXPRESSION;
			}
			}
		} else if (kind == UserDefinedOpKind) {
			return visitUserdefinedOp(s);
		}
		return DefinitionType.EXPRESSION;
	}

	private DefinitionType visitUserdefinedOp(OpApplNode s) {
		OpDefNode def = (OpDefNode) s.getOperator();
		if (BBuiltInOPs.contains(def.getName())
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {

			switch (BBuiltInOPs.getOpcode(def.getName())) {
			case B_OPCODE_lt: // <
			case B_OPCODE_gt: // >
			case B_OPCODE_leq: // <=
			case B_OPCODE_geq: // >=
			case B_OPCODE_finite:
				return DefinitionType.PREDICATE;
			default:
				return DefinitionType.EXPRESSION;
			}

		}
		return getDefinitionType(def);
	}
}
