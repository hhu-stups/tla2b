/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package util;

import java.util.Hashtable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ModelConfig;
import translation.ConfigTypeChecker2;
import translation.Main;
import translation.ModuleContext;
import translation.TypeChecker;
import types.BType;
import util.StandardModules;
import exceptions.FrontEndException;
import exceptions.MyException;

public class TypeCheckerTest {

	public ModuleNode moduleNode;
	public final int toolId = 5;
	private TypeChecker tc;
	public Hashtable<String, BType> constants;
	public Hashtable<String, BType> variables;
	public Hashtable<String, DefCon> definitions;

	public TypeCheckerTest(String fileName, String configName,
			boolean moduleAsString) throws MyException, FrontEndException {

		constants = new Hashtable<String, BType>();
		variables = new Hashtable<String, BType>();
		definitions = new Hashtable<String, DefCon>();

		String moduleName = fileName;
		if (!moduleAsString)
			moduleName = Main.evalFileName(fileName);
		String config = Main.evalConfigName(configName);

		moduleNode = Main.parseModule(moduleName);

		ModuleContext con;
		if (config != null) {
			ModelConfig configAst = new ModelConfig(config + ".cfg", null);
			configAst.parse();

			ConfigTypeChecker2 configTC = new ConfigTypeChecker2(configAst,
					moduleNode);
			configTC.start();
			con = new ModuleContext(moduleNode, configTC);
		}else{
			con = new ModuleContext(moduleNode);
		}
		
		tc = new TypeChecker(moduleNode, con);
	}

	public void start() throws exceptions.FrontEndException, MyException {
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
			if(defCon.getType()== null)
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

	
}
