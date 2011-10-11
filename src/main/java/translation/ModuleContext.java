package translation;

import java.util.ArrayList;
import java.util.Hashtable;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ModelConfig;
import tlc2.util.Vect;
import types.Untyped;

// contains the content of a tla+ module
public class ModuleContext {
	private String spec = "";
	private String next = "";
	private String init = "";
	private ModuleNode rootModule;

	ArrayList<String> invariants = new ArrayList<String>();
	ArrayList<Action> actions = new ArrayList<Action>();
	ArrayList<OpDefNode> lets = new ArrayList<OpDefNode>();

	public Hashtable<String, Constant> constants;
	public Hashtable<String, Variable> variables;
	public Hashtable<String, DefContext> definitions;
	public Hashtable<String, String> overrides;
	public ArrayList<String> setEnumeration;
	
	// Constants which appear in the resulting B machine
	protected ArrayList<String> constantDecl;

	public ModuleContext(ModuleNode rootModule) {
		
		// set root Module
		this.rootModule = rootModule;
		
		// determine the definitions of the module
		evalDefinitions();
		
		// determine the constants of the module
		evalConstants();
		
		/*
		 * Next state relation: if there is no config file use the Next
		 * definition as next state relation for default
		 */
		if(definitions.containsKey("Next")){
			this.next = "Next";
		}
		if(definitions.containsKey("Init")){
			this.init = "Init";
		}
		if(definitions.containsKey("Spec")){
			this.spec = "Spec";
		}
		
		// Overrides
		overrides = new Hashtable<String, String>();

		// set enumeration
		setEnumeration = new ArrayList<String>();

	}

	private void evalConstants() {
		OpDeclNode[] moduleCons = rootModule.getConstantDecls();
		this.constants = new Hashtable<String, Constant>();
		this.constantDecl = new ArrayList<String>();
		for (int i = 0; i < moduleCons.length; i++) {
			OpDeclNode con = moduleCons[i];
			String conName = con.getName().toString();
			this.constants.put(conName, new Constant(conName, new Untyped(), ""));
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
			OpDefNode def = opDefs[i];
			// Definition in this module

			if (!standardModules.contains(def
					.getOriginallyDefinedInModuleNode().getName().toString())) {
				String defName = def.getName().toString();
				definitions.put(defName, new DefContext(defName, def));
			}
		}
	}


	public Hashtable<String, Constant> getConstants() {
		return constants;
	}

	public ModuleNode getRoot() {
		return rootModule;
	}

	public void setRoot(ModuleNode root) {
		this.rootModule = root;
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

	public String toString() {
		String res;
		res = "SPEC: " + this.spec + "\nNEXT: " + this.next + "\nINIT: "
				+ this.init;

		return res;
	}

}
