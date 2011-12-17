package translation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;

import exceptions.ConfigFileErrorException;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ModelConfig;
import tlc2.util.Vect;
import tlc2.value.ModelValue;
import tlc2.value.SetEnumValue;
import types.BType;
import types.BoolType;
import types.IType;
import types.IntType;
import types.ModelValueType;
import types.PowerSetType;
import types.StringType;
import types.Untyped;
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

	public ConfigTypeChecker(ModelConfig configAst, ModuleNode moduleNode) {
		this.configAst = configAst;
		this.moduleNode = moduleNode;

		enumeratedSet = new ArrayList<String>();
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
		evalConstantOverrides();

		// invariant declaration
		evalInvariants();

	}

	private void evalDefinitions() {
		OpDefNode[] opDefs = moduleNode.getOpDefs();
		definitions = new Hashtable<String, OpDefNode>();
		for (int i = 0; i < opDefs.length; i++) {
			OpDefNode def = opDefs[i];
			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
					.getName().toString())
					|| StandardModules.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}
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

	private void evalConstantAssignments() throws ConfigFileErrorException {
		Vect configCons = configAst.getConstants();
		// iterate over all constant declaration in the config file
		for (int i = 0; i < configCons.size(); i++) {
			Vect symbol = (Vect) configCons.elementAt(i);
			String symbolName = symbol.elementAt(0).toString();
			String symbolValue = symbol.elementAt(symbol.size()-1).toString();
			BType symbolType = conGetType(symbol.elementAt(symbol.size()-1));

			if (constants.containsKey(symbolName)) {
				OpDeclNode c = constants.get(symbolName);
				ConstantObj conObj = new ConstantObj(symbolValue, symbolType);
				conObjs.put(symbolName, conObj);
				c.setToolObject(CONSTANT_OBJECT, conObj);
				/**
				 * if conValue is a model value and the name of value is the
				 * same as the name of constants, then the constant declaration
				 * in the resulting B machine disappears
				 **/
				if (symbolName.equals(symbolValue)) {
					bConstants.remove(symbolName);
				}
			} else if (definitions.containsKey(symbolName)) {
				OpDefNode def = definitions.get(symbolName);
				ConstantObj conObj = new ConstantObj(symbolValue, symbolType);
				def.setToolObject(CONSTANT_OBJECT, conObj);
				if (symbolName.equals(symbolValue)) {
					def.setToolObject(PRINT_DEFINITION, false);
				}
				if (symbolName.equals(symbolValue)) {
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
	private void evalConstantOverrides() throws ConfigFileErrorException {
		overrides = configAst.getOverrides();
		Iterator<Map.Entry<String, String>> it = overrides.entrySet()
				.iterator();
		while (it.hasNext()) {
			Map.Entry<String, String> entry = it.next();
			String left = entry.getKey();
			String right = entry.getValue();
			
			if (!definitions.containsKey(right)) {
				throw new ConfigFileErrorException("Invalid substitution for "
						+ left
						+ ".\n Module does not contain definition "
						+ right + ".");
			}
			
			if (constants.containsKey(left)) {
				OpDeclNode con = constants.get(left);
				if (con.getArity() > 0) {
					bConstants.remove(left);
					con.setToolObject(OVERRIDE_SUBSTITUTION_ID, entry.getValue());
					overrides.remove(entry.getKey());
				}
			} else if (definitions.containsKey(left)) {
				OpDefNode def = definitions.get(left);
				ConstantObj conObj = new ConstantObj(right, new Untyped());
				def.setToolObject(CONSTANT_OBJECT, conObj);
			}else {
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
			PowerSetType t = new PowerSetType(ModelValueType.getInstance());
			if (set.size() == 0) {
				throw new ConfigFileErrorException(
						"empty set is not permitted!");
			}
			BType elemType = conGetType(set.elems.elementAt(0));
			t.setSubType(elemType);

			for (int i = 1; i < set.size(); i++) {
				elemType = conGetType(set.elems.elementAt(i));
				// all Elements have the same Type?
				if (!t.getSubType().equals(elemType)) {
					throw new ConfigFileErrorException(
							"Elements of the set must have the same type: " + o);
				}
			}
			return t;

		} else if (o.getClass().getName().equals("tlc2.value.ModelValue")) {
			ModelValue mv = (ModelValue) o;

			if (!enumeratedSet.contains(mv.toString())) {
				enumeratedSet.add(mv.toString());
			}
			return ModelValueType.getInstance();
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

}
