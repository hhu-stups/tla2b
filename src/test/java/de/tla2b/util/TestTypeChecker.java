/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.util;

import java.util.Hashtable;

import de.tla2b.analysis.TypeChecker;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.translation.Tla2BTranslator;
import de.tla2b.types.TLAType;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;

public class TestTypeChecker implements TranslationGlobals {

	public ModuleNode moduleNode;
	public final int toolId = 5;
	private Hashtable<String, TLAType> constants;
	private Hashtable<String, TLAType> variables;
	private Hashtable<String, DefCon> definitions;

	public TestTypeChecker() {
		constants = new Hashtable<String, TLAType>();
		variables = new Hashtable<String, TLAType>();
		definitions = new Hashtable<String, DefCon>();
	}

	public void startTest(String moduleString, String configString)
			throws FrontEndException, TLA2BException {
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.startTest(moduleString, configString);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}
	
	public void start(String moduleFileName, String configFileName)
			throws FrontEndException, TLA2BException {
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.start(moduleFileName, configFileName);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}

	private void init() {
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode con = moduleNode.getConstantDecls()[i];
			constants.put(con.getName().toString(),
					(TLAType) con.getToolObject(toolId));
		}

		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode var = moduleNode.getVariableDecls()[i];
			variables.put(var.getName().toString(),
					(TLAType) var.getToolObject(toolId));
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			DefCon defCon = new DefCon((TLAType) def.getToolObject(5));
			if (defCon.getType() == null)
				continue;

			if (STANDARD_MODULES.contains(def
					.getOriginallyDefinedInModuleNode().getName().toString())
					|| STANDARD_MODULES.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}

			for (int j = 0; j < def.getParams().length; j++) {
				FormalParamNode p = def.getParams()[j];
				defCon.parameters.put(p.getName().toString(),
						(TLAType) p.getToolObject(toolId));
			}
			definitions.put(def.getName().toString(), defCon);
		}
	}

	
	public String getConstantType(String conName) {
		return constants.get(conName).toString();
	}
	
	public String getVariableType(String varName){
		return variables.get(varName).toString();
	}

	public String getDefinitionType(String defName){
		return definitions.get(defName).getType().toString();
	}

	public String getDefinitionParamType(String defName, String paramName){
		return definitions.get(defName).getParams().get(paramName).toString();
	}

	public class DefCon {
		private Hashtable<String, TLAType> parameters;
		private TLAType type;

		private DefCon(TLAType t) {
			parameters = new Hashtable<String, TLAType>();
			type = t;
		}

		public Hashtable<String, TLAType> getParams() {
			return parameters;
		}

		public TLAType getType() {
			return type;
		}

		public void setType(TLAType type) {
			this.type = type;
		}
	}
}
