package translation;

import java.util.ArrayList;
import java.util.Hashtable;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import types.Untyped;

// contains the content of a tla+ module
public class ModuleContext {
	private String spec;
	private String next;
	private String init;
	private ModuleNode rootModule;
	private Hashtable<String, DefContext> definitions;
	private Hashtable<String, Variable> variables;
	private Hashtable<String, Constant> constants;

	
	// Constants which appear in the resulting B machine
	private ArrayList<String> constantDecl;
	
	protected Hashtable<String, String> overrides;
	protected ArrayList<String> setEnumeration;
	
	
	protected ArrayList<String> invariants = new ArrayList<String>();
	protected ArrayList<Action> actions = new ArrayList<Action>();
	protected ArrayList<OpDefNode> lets = new ArrayList<OpDefNode>();

	



	public ModuleContext(ModuleNode rootModule, String config) {

		// set root Module
		this.rootModule = rootModule;

		// determine the definitions of the module
		evalDefinitions();

		// determine the constants of the module
		evalConstants();

		evalVariables();

		/*
		 * Conventions: if there is no config file use the 'Next' as next state
		 * relation, 'Init' as initialisation predicate or 'Spec' as module
		 * specification
		 */
		if (config == null) {
			if (definitions.containsKey("Spec")) {
				this.spec = "Spec";
			}
			if (this.spec == null) {
				if (definitions.containsKey("Next")) {
					this.next = "Next";
				}
				if (definitions.containsKey("Init")) {
					this.init = "Init";
				}
			}
		}

		// Overrides
		overrides = new Hashtable<String, String>();

		// set enumeration
		setEnumeration = new ArrayList<String>();

	}

	private void evalVariables() {
		OpDeclNode[] vars = rootModule.getVariableDecls();
		this.variables = new Hashtable<String, Variable>();
		if (vars.length > 0) {
			for (int i = 0; i < vars.length; i++) {
				String var = vars[i].getName().toString();
				variables.put(var, new Variable(var, new Untyped()));
			}

		}
	}

	private void evalConstants() {
		OpDeclNode[] moduleCons = rootModule.getConstantDecls();
		this.constants = new Hashtable<String, Constant>();
		this.constantDecl = new ArrayList<String>();
		for (int i = 0; i < moduleCons.length; i++) {
			OpDeclNode con = moduleCons[i];
			String conName = con.getName().toString();
			this.constants.put(conName,
					new Constant(conName, new Untyped(), ""));
			this.constantDecl.add(conName);
		}
	}

	private void evalDefinitions() {
		OpDefNode[] opDefs = rootModule.getOpDefs();
		ArrayList<String> standardModules = new ArrayList<String>();
		standardModules.add("TLC");
		standardModules.add("Naturals");
		standardModules.add("FiniteSets");
		standardModules.add("Sequences");

		definitions = new Hashtable<String, DefContext>();
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode defNode = opDefs[i];
			// Definition in this module
			if (!standardModules.contains(defNode
					.getOriginallyDefinedInModuleNode().getName().toString())) {
				
				if (standardModules.contains(defNode.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
					continue;
				}
				evalDefintion(defNode);
			}
		}
	}

	private void evalDefintion(OpDefNode defNode) {
		
		String defName = defNode.getName().toString();
		DefContext defCon = new DefContext(defName, defNode);
		String prefix = null;
		if (defName.contains("!")) {
			prefix = defName.substring(0, defName.lastIndexOf('!'));
			defCon.setPrefix(prefix);
		}
		defCon.setParams(evalParams(defNode.getParams()));
		definitions.put(defName, defCon);
	}

	private String[] evalParams(FormalParamNode[] params) {
		String[] res = new String[params.length];
		for (int i = 0; i < params.length; i++) {
			res[i] = params[i].getName().toString();
		}
		return res;
	}

	public Hashtable<String, Constant> getConstants() {
		return constants;
	}

	public ModuleNode getRoot() {
		return rootModule;
	}

	public ArrayList<String> getInvariants() {
		return invariants;
	}

	public String getSpec() {
		return spec;
	}

	public void setSpec(String spec) {
		this.spec = spec;
	}

	public String getNext() {
		return next;
	}

	public void setNext(String next) {
		this.next = next;
	}

	public String getInit() {
		return init;
	}

	public void setInit(String init) {
		this.init = init;
	}

	public DefContext getDef(String defName) {
		return definitions.get(defName);
	}

	public boolean containsDef(String defName) {
		return definitions.containsKey(defName);
	}

	public Variable getVar(String valName) {
		return variables.get(valName);
	}

	public Constant getCon(String conName) {
		return constants.get(conName);
	}

	public boolean containsCon(String conName){
		return constants.containsKey(conName);
	}
	
	public void removeBCon(String conName){
		constantDecl.remove(conName);
	}
	
	public ArrayList<String> getBConstants(){
		ArrayList<String> clone = new ArrayList<String>(constantDecl);
		return clone;
	}
	
	
	public void setOverrides(Hashtable<String, String> overrides) {
		this.overrides = overrides;
	}
	public Hashtable<String, String> getOverrides(){
		return this.overrides;
	}
	
	public void addEnum(String modelValue){
		setEnumeration.add(modelValue);
	}
	
	public boolean containsEnum(String modelValue){
		return setEnumeration.contains(modelValue);
	}
	
	public ArrayList<String> getEnum(){
		return setEnumeration;
	}
	

	public String toString() {
		String res;
		res = "SPEC: " + this.spec + "\nNEXT: " + this.next + "\nINIT: "
				+ this.init;

		return res;
	}

}
