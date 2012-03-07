package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import exceptions.ConfigFileErrorException;
import exceptions.UnificationException;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tlc2.tool.ModelConfig;
import tlc2.util.Vect;
import tlc2.value.ModelValue;
import tlc2.value.SetEnumValue;
import types.AbstractHasFollowers;
import types.BType;
import types.BoolType;
import types.IType;
import types.IntType;
import types.PowerSetType;
import types.StringType;
import types.Untyped;
import types.EnumType;
import util.StandardModules;

public class ConfigTypeChecker implements IType, TranslationGlobals {
	private ModuleNode moduleNode;
	private ModelConfig configAst;

	private String spec;
	private String next;
	private String init;

	private Hashtable<String, OpDefNode> definitions;
	private Hashtable<String, OpDeclNode> constants;

	private ArrayList<String> bConstants;
	private ArrayList<String> invariants;
	private Hashtable<String, ConstantObj> conObjs;
	private Hashtable<String, String> overrides;
	private ArrayList<String> enumeratedSet;
	private LinkedHashMap<String, EnumType> enumeratedTypes;

	public ConfigTypeChecker(ModelConfig configAst, ModuleNode moduleNode) {
		this.configAst = configAst;
		this.moduleNode = moduleNode;

		this.enumeratedSet = new ArrayList<String>();
		this.enumeratedTypes = new LinkedHashMap<String, EnumType>();
		evalDefinitions();
	}

	public void start() throws ConfigFileErrorException {
		// next declaration
		evalNext();

		// init declaration
		evalInit();

		// spec declatation
		evalSpec();

		// constants
		OpDeclNode[] cons = moduleNode.getConstantDecls();
		constants = new Hashtable<String, OpDeclNode>();
		for (int i = 0; i < cons.length; i++) {
			constants.put(cons[i].getName().toString(), cons[i]);
		}
		bConstants = new ArrayList<String>(constants.keySet());
		conObjs = new Hashtable<String, ConstantObj>();

		// constant assignments
		evalConstantAssignments();

		// constant overrides
		evalConstantOrDefOverrides();

		evalModConstantsAssignments();

		// invariant declaration
		evalInvariants();

	}

	private void evalDefinitions() {
		OpDefNode[] opDefs = moduleNode.getOpDefs();
		definitions = new Hashtable<String, OpDefNode>();
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
//			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
//					.getName().toString())
//					|| StandardModules.contains(def.getSource()
//							.getOriginallyDefinedInModuleNode().getName()
//							.toString())) {
//				continue;
//			}
			definitions.put(def.getName().toString(), def);
		}
	}

	private void evalInvariants() throws ConfigFileErrorException {
		invariants = new ArrayList<String>();
		Vect v = configAst.getInvariants();
		for (int i = 0; i < v.capacity(); i++) {
			if (v.elementAt(i) != null) {
				String inv = (String) v.elementAt(i);
				if (!definitions.containsKey(inv)) {
					throw new ConfigFileErrorException(
							"Invalid invariant declaration. Module does not contain definition '"
									+ inv + "'");
				}
				invariants.add(inv);
			}
		}
	}

	private void evalSpec() throws ConfigFileErrorException {
		String spec = configAst.getSpec();
		if (!spec.equals("")) {
			if (definitions.containsKey(spec)) {
				this.spec = spec;
			} else {
				throw new ConfigFileErrorException(
						"Module does not contain the defintion '" + spec + "'");
			}
		} else
			spec = null;
	}

	private void evalNext() throws ConfigFileErrorException {
		String next = configAst.getNext();
		if (!next.equals("")) {
			if (definitions.containsKey(next)) {
				this.next = next;
			} else {
				throw new ConfigFileErrorException(
						"Module does not contain the defintion '" + next + "'");
			}
		} else
			next = null;

	}

	private void evalInit() throws ConfigFileErrorException {
		// Init
		String init = configAst.getInit();
		// no init predicate but variables in the module, which needs to be
		// initialized
		if (init.equals("")) {
			init = null;
			return;
		}
		if (definitions.containsKey(init)) {
			this.init = init;
		} else {
			throw new ConfigFileErrorException(
					"Invalid declaration of the initialisation predicate. Module does not contain the defintion '"
							+ init + "'");
		}

	}

	private void evalModConstantsAssignments() throws ConfigFileErrorException {
		// val = [Counter] 7
		@SuppressWarnings("unchecked")
		Hashtable<String, Vect> configCons = configAst.getModConstants();
		Enumeration<String> moduleNames = configCons.keys();
		while (moduleNames.hasMoreElements()) {
			String moduleName = (String) moduleNames.nextElement();
			ModuleNode mNode = searchModule(moduleName);
			Vect assignments = configCons.get(moduleName);
			for (int i = 0; i < assignments.size(); i++) {
				Vect assigment = (Vect) assignments.elementAt(i);
				OpDefOrDeclNode opDefOrDeclNode = searchDefinitionOrConstant(
						mNode, (String) assigment.elementAt(0));
				String symbolName = opDefOrDeclNode.getName().toString();
				Object symbolValue = assigment.elementAt(1);
				BType symbolType = conGetType(assigment.elementAt(1));
				// System.out.println(symbolName + " " + symbolValue+ " " +
				// symbolType);

				if (opDefOrDeclNode instanceof OpDeclNode) {
					OpDeclNode c = (OpDeclNode) opDefOrDeclNode;
					if (symbolType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) symbolType).addFollower(c);
					}
					ConstantObj conObj = new ConstantObj(symbolValue,
							symbolType);
					conObjs.put(symbolName, conObj);
					c.setToolObject(CONSTANT_OBJECT, conObj);
					/**
					 * if conValue is a model value and the name of value is the
					 * same as the name of constants, then the constant
					 * declaration in the resulting B machine disappears
					 **/
					if (symbolName.equals(symbolValue.toString())) {
						bConstants.remove(symbolName);
						conObjs.put(symbolName, conObj);
					}
				} else {
					OpDefNode def = (OpDefNode) opDefOrDeclNode;
					ConstantObj conObj = new ConstantObj(symbolValue,
							symbolType);
					def.setToolObject(CONSTANT_OBJECT, conObj);
					if (symbolName.equals(symbolValue.toString())) {
						def.setToolObject(PRINT_DEFINITION, false);
					}
				}
			}
		}
	}

	public ModuleNode searchModule(String moduleName)
			throws ConfigFileErrorException {
		InstanceNode[] instanceNodes = moduleNode.getInstances();

		for (int i = 0; i < instanceNodes.length; i++) {
			if (instanceNodes[i].getModule().getName().toString()
					.equals(moduleName))
				return instanceNodes[i].getModule();
		}
		throw new ConfigFileErrorException(
				String.format(
						"Module '%s' is not included in the specification.",
						moduleName));
	}

	public OpDefOrDeclNode searchDefinitionOrConstant(ModuleNode n,
			String defOrConName) throws ConfigFileErrorException {
		for (int i = 0; i < n.getOpDefs().length; i++) {
			if (n.getOpDefs()[i].getName().toString().equals(defOrConName)) {
				return n.getOpDefs()[i];
			}
		}
		for (int i = 0; i < n.getConstantDecls().length; i++) {
			if (n.getConstantDecls()[i].getName().toString()
					.equals(defOrConName)) {
				return n.getConstantDecls()[i];
			}
		}
		throw new ConfigFileErrorException(
				"Module does not contain the symbol: " + defOrConName);
	}

	private void evalConstantAssignments() throws ConfigFileErrorException {
		Vect configCons = configAst.getConstants();
		// iterate over all constant declaration in the config file
		for (int i = 0; i < configCons.size(); i++) {
			Vect symbol = (Vect) configCons.elementAt(i);
			String symbolName = symbol.elementAt(0).toString();
			Object symbolValue = symbol.elementAt(symbol.size() - 1);
			BType symbolType = conGetType(symbol.elementAt(symbol.size() - 1));
			if (constants.containsKey(symbolName)) {
				OpDeclNode c = constants.get(symbolName);
				if (symbolType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) symbolType).addFollower(c);
				}
				ConstantObj conObj = new ConstantObj(symbolValue, symbolType);
				conObjs.put(symbolName, conObj);
				c.setToolObject(CONSTANT_OBJECT, conObj);
				/**
				 * if conValue is a model value and the name of value is the
				 * same as the name of constants, then the constant declaration
				 * in the resulting B machine disappears
				 **/
				if (symbolName.equals(symbolValue.toString())) {
					bConstants.remove(symbolName);
					conObjs.put(symbolName, conObj);
				}
			} else if (definitions.containsKey(symbolName)) {
				OpDefNode def = definitions.get(symbolName);
				ConstantObj conObj = new ConstantObj(symbolValue, symbolType);
				def.setToolObject(CONSTANT_OBJECT, conObj);
				if (symbolName.equals(symbolValue.toString())) {
					def.setToolObject(PRINT_DEFINITION, false);
				}
			} else {
				// every constants in the config file must appear in the TLA+
				// module
				throw new ConfigFileErrorException(
						"Module does not contain the symbol: " + symbolName);
			}
		}
	}

	@SuppressWarnings("unchecked")
	private void evalConstantOrDefOverrides() throws ConfigFileErrorException {
		overrides = (Hashtable<String, String>) configAst.getOverrides()
				.clone();
		Iterator<Map.Entry<String, String>> it = configAst.getOverrides()
				.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry<String, String> entry = it.next();
			String left = entry.getKey();
			String right = entry.getValue();

			// Verify if the definition on the right is a valid definition
			if (!definitions.containsKey(right)) {
				throw new ConfigFileErrorException("Invalid substitution for "
						+ left + ".\n Module does not contain definition "
						+ right + ".");
			}

			if (constants.containsKey(left)) {
				OpDeclNode con = constants.get(left);
				if (con.getArity() > 0) {
					bConstants.remove(left);
					con.setToolObject(OVERRIDE_SUBSTITUTION_ID,
							entry.getValue());
					overrides.remove(entry.getKey());
				}
			} else if (definitions.containsKey(left)) {
				OpDefNode def = definitions.get(left);
				// TODO remove conObj
				ConstantObj conObj = new ConstantObj(right, new Untyped());
				def.setToolObject(CONSTANT_OBJECT, conObj);
				def.setToolObject(DEF_OBJECT, definitions.get(right));
				overrides.remove(entry.getKey());
			} else {
				// every constants in the config file must appear in the TLA+
				// module
				throw new ConfigFileErrorException(
						"Module does not contain the symbol: " + left);
			}

		}

	}

	private BType conGetType(Object o) throws ConfigFileErrorException {
		if (o.getClass().getName().equals("tlc2.value.IntValue")) {
			// IntValue iv = (IntValue) o;
			return IntType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.SetEnumValue")) {
			SetEnumValue set = (SetEnumValue) o;
			PowerSetType t = new PowerSetType(new Untyped());
			if (set.size() == 0) {
				throw new ConfigFileErrorException(
						"empty set is not permitted!");
			}
			BType elemType;

			if (set.elems.elementAt(0).getClass().getName()
					.equals("tlc2.value.ModelValue")) {
				EnumType e = new EnumType(new ArrayList<String>());
				for (int i = 0; i < set.size(); i++) {
					if (set.elems.elementAt(i).getClass().getName()
							.equals("tlc2.value.ModelValue")) {
						String mv = ((ModelValue) set.elems.elementAt(i))
								.toString();
						if (!enumeratedSet.contains(mv)) {
							enumeratedSet.add(mv);
							e.modelvalues.add(mv);
						} else {
							e.modelvalues.add(mv);
							EnumType e2 = enumeratedTypes.get(mv);
							try {
								e = e2.unify(e2);
							} catch (UnificationException exception) {
							}
						}

					} else {
						throw new ConfigFileErrorException(
								"Elements of the set must have the same type: "
										+ o);
					}
				}
				Iterator<String> it = e.modelvalues.iterator();
				while (it.hasNext()) {
					enumeratedTypes.put(it.next(), e);
				}
				elemType = e;
			} else {
				elemType = conGetType(set.elems.elementAt(0));
				for (int i = 1; i < set.size(); i++) {
					elemType = conGetType(set.elems.elementAt(i));
					// all Elements have the same Type?
					if (!t.getSubType().compare(elemType)) {
						throw new ConfigFileErrorException(
								"Elements of the set must have the same type: "
										+ o);
					}
				}
			}
			t.setSubType(elemType);
			return t;

		} else if (o.getClass().getName().equals("tlc2.value.ModelValue")) {
			ModelValue mv = (ModelValue) o;

			if (!enumeratedSet.contains(mv.toString())) {
				enumeratedSet.add(mv.toString());
				ArrayList<String> temp = new ArrayList<String>();
				temp.add(mv.toString());
				EnumType e = new EnumType(temp);
				enumeratedTypes.put(mv.toString(), e);
				return e;
			} else {
				return enumeratedTypes.get(mv.toString());
			}

		} else if (o.getClass().getName().equals("tlc2.value.StringValue")) {
			return StringType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.BoolValue")) {
			return BoolType.getInstance();
		} else {
			throw new ConfigFileErrorException("Unkown ConstantType: " + o
					+ " " + o.getClass());
		}
	}

	public String getSpec() {
		return spec;
	}

	public String getNext() {
		return next;
	}

	public String getInit() {
		return init;
	}

	public ArrayList<String> getbConstants() {
		return bConstants;
	}

	public ArrayList<String> getInvariants() {
		return invariants;
	}

	public Hashtable<String, ConstantObj> getConObjs() {
		return conObjs;
	}

	public Hashtable<String, String> getOverrides() {
		return overrides;
	}

	public ArrayList<String> getEnumeratedSet() {
		return enumeratedSet;
	}

	public LinkedHashMap<String, EnumType> getEnumeratedTypes() {
		return enumeratedTypes;
	}
}
