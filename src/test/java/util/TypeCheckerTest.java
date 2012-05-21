/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package util;

import java.util.Hashtable;

import analysis.InstanceTransformation;
import analysis.NewTypeChecker;
import analysis.SpecAnalyser;
import analysis.SymbolSorter;

import config.ConfigfileEvaluator;
import config.ModuleOverrider;


import tla2sany.semantic.AbortException;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ModelConfig;
import translation.Main;
import types.BType;
import util.StandardModules;
import exceptions.FrontEndException;
import exceptions.TLA2BException;

public class TypeCheckerTest {

	public ModuleNode moduleNode;
	public final int toolId = 5;
	private NewTypeChecker tc;
	public Hashtable<String, BType> constants;
	public Hashtable<String, BType> variables;
	public Hashtable<String, DefCon> definitions;

	public TypeCheckerTest(String fileName, String configName,
			boolean moduleAsString) throws TLA2BException, FrontEndException {

		constants = new Hashtable<String, BType>();
		variables = new Hashtable<String, BType>();
		definitions = new Hashtable<String, DefCon>();

		String moduleName = fileName;
		if (!moduleAsString)
			moduleName = Main.evalFileName(fileName);
		// String config = Main.evalConfigName(configName);

		moduleNode = Main.parseModule(moduleName);

		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		try {
			trans.start();
		} catch (AbortException e) {
			e.printStackTrace();
		}

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();

		SpecAnalyser specAnalyser;
		ConfigfileEvaluator conEval = null;
		if (configName != null) {
			ModelConfig configAst = new ModelConfig(configName, null);
			configAst.parse();

			conEval = new ConfigfileEvaluator(configAst, moduleNode);
			conEval.start();

			ModuleOverrider modOver = new ModuleOverrider(moduleNode,
					conEval.getConstantOverrideTable(),
					conEval.getOperatorOverrideTable(),
					conEval.getOperatorAssignments());
			modOver.start();
			specAnalyser = new SpecAnalyser(moduleNode, conEval);
		}else {
			specAnalyser = new SpecAnalyser(moduleNode);
		}

		specAnalyser.start();

		tc = new NewTypeChecker(moduleNode, conEval,
				specAnalyser);
	}

	public void start() throws exceptions.FrontEndException, TLA2BException {
		tc.start();

		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode con = moduleNode.getConstantDecls()[i];
			constants.put(con.getName().toString(),
					(BType) con.getToolObject(toolId));
		}

		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode var = moduleNode.getVariableDecls()[i];
			variables.put(var.getName().toString(),
					(BType) var.getToolObject(toolId));
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			DefCon defCon = new DefCon((BType) def.getToolObject(5));
			if (defCon.getType() == null)
				continue;

			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
					.getName().toString())
					|| StandardModules.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}

			for (int j = 0; j < def.getParams().length; j++) {
				FormalParamNode p = def.getParams()[j];
				defCon.parameters.put(p.getName().toString(),
						(BType) p.getToolObject(toolId));
			}
			definitions.put(def.getName().toString(), defCon);
		}

	}
	
	public class DefCon {
			private Hashtable<String, BType> parameters;
			private BType type;
			
			private DefCon(BType t){
				parameters = new Hashtable<String, BType>();
				type = t;
			}

			public Hashtable<String, BType> getParams(){
				return parameters;
			}
			
			public BType getType() {
				return type;
			}

			public void setType(BType type) {
				this.type = type;
			}
		}
}
