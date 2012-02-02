/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;
import java.util.Hashtable;

import exceptions.FrontEndException;
import exceptions.SemanticErrorException;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class SpecAnalyser implements ASTConstants, ToolGlobals, TranslationGlobals{
	private String spec;
	private Hashtable<String, OpDefNode> definitions;
	private ArrayList<BInit> inits;
	private ExprNode nextExpr;
	private String nextName;
	
	private String init;
	private String next;
	
	/**
	 * 
	 */
	public SpecAnalyser(String spec, String init, String next, Hashtable<String, OpDefNode> definitions) {
		this.spec = spec;
		this.init = init;
		this.next = next;
		this.definitions = definitions;
	}
	
	public void start() throws SemanticErrorException, FrontEndException{
		if(spec != null && definitions.containsKey(spec)){
			evalSpec();
		}else{
			evalInit(this.init);
			evalNext(this.next);
		}
	}
	
	private void evalInit(String defName) {
		inits = new ArrayList<BInit>();
		if (defName == null)
			return;

		if (definitions.containsKey(defName)) {
			OpDefNode init = definitions.get(defName);
			init.setToolObject(PRINT_DEFINITION, false);
			inits.add(new BInit("", init.getBody()));
		}
	}
	
	private void evalNext(String defName) throws FrontEndException {
		if (defName == null)
			return;

		if (definitions.containsKey(defName)) {
			OpDefNode next = definitions.get(defName);
			next.setToolObject(PRINT_DEFINITION, false);
			this.nextExpr = next.getBody();
			this.nextName = defName;
		}
	}
	
	public void evalSpec() throws SemanticErrorException, FrontEndException{
		inits = new ArrayList<BInit>();
		OpDefNode def = definitions.get(spec);
		ExprNode e = def.getBody();
		processConfigSpec(e, "");
	}
	
	
	private void processConfigSpec(ExprNode exprNode, String prefix)
			throws SemanticErrorException, FrontEndException {

		if (exprNode instanceof SubstInNode) {
			SubstInNode substInNode = (SubstInNode) exprNode;
			processConfigSpec(substInNode.getBody(), prefix);
			return;
		}

		if (exprNode instanceof OpApplNode) {
			OpApplNode opApp = (OpApplNode) exprNode;
			ExprOrOpArgNode[] args = opApp.getArgs();
			if (args.length == 0) {
				SymbolNode opNode = opApp.getOperator();
				if (opNode instanceof OpDefNode) {
					OpDefNode def = (OpDefNode) opNode;
					ExprNode body = def.getBody();
					if (body.getLevel() == 1) {
						inits.add(new BInit(prefix, exprNode));
					} else {
						String defName = def.getName().toString();
						String newPrefix = prefix
								+ defName.substring(0,
										defName.lastIndexOf('!') + 1);
						processConfigSpec(body, newPrefix);
					}
					return;
				}
				throw new SemanticErrorException(
						"Can not handle specification conjunction.");
			}

			int opcode = BuiltInOPs.getOpCode(opApp.getOperator().getName());
			if (opcode == OPCODE_cl || opcode == OPCODE_land) {
				for (int i = 0; i < args.length; i++) {
					this.processConfigSpec((ExprNode) args[i], prefix);
				}
				return;
			}

			if (opcode == OPCODE_box) {
				SemanticNode boxArg = args[0];
				if ((boxArg instanceof OpApplNode)
						&& BuiltInOPs.getOpCode(((OpApplNode) boxArg)
								.getOperator().getName()) == OPCODE_sa) {
					ExprNode next = (ExprNode) ((OpApplNode) boxArg).getArgs()[0];
					this.nextExpr = next;
					this.nextName = "Next";
					return;
				}
			}
		}

		if (exprNode.getLevel() <= 1) {
			// init
			inits.add(new BInit(prefix, exprNode));
		} else if (exprNode.getLevel() == 3) {
			// temporal

		} else {
			throw new SemanticErrorException(
					"Can not handle specification conjunction.");
		}

	}

	public ExprNode getNextExpr() {
		return nextExpr;
	}


	public String getNextName() {
		return nextName;
	}

	public ArrayList<BInit> getInits(){
		return inits;
	}
}
