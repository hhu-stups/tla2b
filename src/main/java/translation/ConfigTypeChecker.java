package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

import exceptions.ConfigFileErrorException;

import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import tlc2.util.Vect;
import tlc2.value.ModelValue;
import tlc2.value.SetEnumValue;
import types.*;

//Analyse Konfigurationsdatei
public class ConfigTypeChecker implements IType {
	private ModuleNode rootModule;
	private ModelConfig configAst;

	private ModuleContext moduleContext;

	@SuppressWarnings("unchecked")
	public ConfigTypeChecker(ModelConfig configAst, ModuleContext moduleContext) {
		this.moduleContext = moduleContext;
		this.configAst = configAst;

		// no default values for init, next and spec
		this.moduleContext.setNext("");
		this.moduleContext.setInit("");
		this.moduleContext.setSpec("");
	}

	@SuppressWarnings("unchecked")
	public void start() throws ConfigFileErrorException {
		// next declaration
		evalNext();

		// init declaration
		evalInit();

		// spec declatation
		evalSpec();

		// constant assignments
		evalConstantAssignments();

		// constant overrides
		evalConstantOverrides();

		duplicateIdentifier(rootModule);

		// invariant declaration
		evalInvariants();

	}

	private void evalInvariants() throws ConfigFileErrorException {
		Vect v = configAst.getInvariants();
		for (int i = 0; i < v.capacity(); i++) {
			if (v.elementAt(i) != null) {
				String inv = (String) v.elementAt(i);
				if (!moduleContext.definitions.containsKey(inv)) {
					throw new ConfigFileErrorException(
							"Invalid invariant declaration. Module does not contain definition '"
									+ inv + "'");
				}
				moduleContext.invariants.add(inv);
			}
		}
	}

	private void evalSpec() throws ConfigFileErrorException {
		String spec = configAst.getSpec();
		if (moduleContext.definitions.containsKey(spec)) {
			moduleContext.setSpec(spec);
		} else if (!spec.equals("")) {
			throw new ConfigFileErrorException(
					"Module does not contain the defintion '" + spec + "'");
		}
	}

	private void evalNext() throws ConfigFileErrorException {
		String next = configAst.getNext();
		if (moduleContext.definitions.containsKey(next)) {
			moduleContext.setNext(next);
		} else if (!next.equals("")) {
			throw new ConfigFileErrorException(
					"Module does not contain the defintion '" + next + "'");
		}
	}

	private void evalInit() throws ConfigFileErrorException {
		// Init
		String init = configAst.getInit();
		// no init predicate but variables in the module, which needs to be
		// initialized
		if (init.equals("")
				&& moduleContext.getRoot().getVariableDecls().length > 0) {
			throw new ConfigFileErrorException(
					"No initialisation predicate in the configuration file");
		}

		if (moduleContext.definitions.containsKey(init)) {
			moduleContext.setInit(init);
		} else if (!init.equals("")) {
			throw new ConfigFileErrorException(
					"Invalid declaration of the initialisation predicate. Module does not contain the defintion '"
							+ init + "'");
		}

	}

	private void evalConstantAssignments() throws ConfigFileErrorException {
		Vect configCons = configAst.getConstants();
		// iterate over all constant declaration in the config file
		for (int i = 0; i < configCons.size(); i++) {
			Vect constant = (Vect) configCons.elementAt(i);
			String conName = constant.elementAt(0).toString();

			// every constants in the config file must appear in the TLA+ module
			if (!moduleContext.constantDecl.contains(conName)) {
				throw new ConfigFileErrorException(
						"Module does not contain this constant: " + conName);
			}

			String conValue = constant.elementAt(1).toString();
			MyType conType = ConGetType(constant.elementAt(1));

			Constant conObj = moduleContext.constants.get(conName);
			conObj.setValue(conValue);
			conObj.setType(conType);

			// if conValue is a model value and the name of value is the same as
			// the name of constants, then the constant declaration in the
			// resulting B machine disappears
			if (conName.equals(conValue)) {
				moduleContext.constantDecl.remove(conName);
			}
		}

	}

	@SuppressWarnings("unchecked")
	private void evalConstantOverrides() throws ConfigFileErrorException {
		moduleContext.overrides = configAst.getOverrides();
		
		Hashtable<String, String> over = configAst.getOverrides();
		Enumeration<String> keys = over.keys();
		Enumeration<String> values = over.elements();
		while (keys.hasMoreElements()) {
			String conName = keys.nextElement();
			String conValue = values.nextElement();
			if (moduleContext.definitions.containsKey(conValue)) {
				Constant con = moduleContext.constants.get(conName);
				con.setValue(conValue);
			} else {
				throw new ConfigFileErrorException("Invalid substitution for "
						+ conName + "\n module does not contain definition "
						+ conValue);
			}

		}
		
	}

	private void duplicateIdentifier(ModuleNode module)
			throws ConfigFileErrorException {
		// TODO ????
		// for (String elem : moduleContext.setEnumeration) {
		// if (constantDecl.contains(elem)) {
		// throw new ConfigFileErrorException("Identifier '" + elem
		// + "' declared twice");
		// }
		// }
	}

	private MyType ConGetType(Object o) throws ConfigFileErrorException {
		if (o.getClass().getName().equals("tlc2.value.IntValue")) {
			// IntValue iv = (IntValue) o;
			return new IntType();
		} else if (o.getClass().getName().equals("tlc2.value.SetEnumValue")) {
			SetEnumValue set = (SetEnumValue) o;
			PowerSetType t = new PowerSetType(new ModelValueType());
			if (set.size() == 0) {
				throw new ConfigFileErrorException("empty set is not permitted!");
			}
			MyType elemType = ConGetType(set.elems.elementAt(0));
			t.setSubType(elemType);

			for (int i = 1; i < set.size(); i++) {
				elemType = ConGetType(set.elems.elementAt(i));
				// all Elements have the same Type?
				if (!t.getSubType().equals(elemType)) {
					throw new ConfigFileErrorException(
							"Elements of the set must have the same type: " + o);
				}
			}
			return t;

		} else if (o.getClass().getName().equals("tlc2.value.ModelValue")) {
			ModelValue mv = (ModelValue) o;
			if (!moduleContext.setEnumeration.contains(mv.toString())) {
				moduleContext.setEnumeration.add(mv.toString());
			}
			return new ModelValueType();
		} else if (o.getClass().getName().equals("tlc2.value.StringValue")) {
			return new StringType();
		} else if (o.getClass().getName().equals("tlc2.value.BoolValue")) {
			return new BooleanType();
		} else {
			System.out.println("ModeltypeChecker Error" + o + " "
					+ o.getClass());
			return null;
		}

	}
}
