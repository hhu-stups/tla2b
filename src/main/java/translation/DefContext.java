package translation;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpDefNode;
import types.MyType;
import types.Untyped;

//contains the content of a TLA+-definition
public class DefContext {
	private boolean next = false;
	private String[] params;
	private MyType type;
	private String name;
	private boolean isEquation;
	private boolean temporal;
	private OpDefNode node;
	private String prefix;
	public Hashtable<String, Parameter> temp = new Hashtable<String, Parameter>();
	public Hashtable<String, Subdefinition> lets = new Hashtable<String, Subdefinition>();
	public Hashtable<String, Parameter> parameters = new Hashtable<String, Parameter>();
	public Hashtable<String, ExprOrOpArgNode> substitution = new Hashtable<String, ExprOrOpArgNode>();

	public DefContext(String n) {
		name = n;
	}

	public OpDefNode getNode() {
		return node;
	}

	public void setNode(OpDefNode node) {
		this.node = node;
	}

	public DefContext(String n, OpDefNode node) {
		name = n;
		this.node = node;
		this.type = new Untyped();
	}

	public DefContext() {
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getPrefix() {
		return prefix;
	}

	public void setPrefix(String prefix) {
		this.prefix = prefix;
	}

	public boolean isNext() {
		return next;
	}

	public String[] getParams() {
		return params;
	}

	public void setParams(String[] params) {
		this.params = params;
		parameters = new Hashtable<String, Parameter>();
		for (int i = 0; i < params.length; i++) {
			parameters.put(params[i], new Parameter(new Untyped()));

		}
	}

	public void setParams(ArrayList<String> params2) {
		this.params = new String[params2.size()];
		parameters = new Hashtable<String, Parameter>();
		for (int i = 0; i < params2.size(); i++) {
			String param = params2.get(i);
			this.params[i] = param;
			parameters.put(param, new Parameter(new Untyped()));
		}
	}

	public void addParams(ArrayList<String> params2) {
		this.params = new String[params2.size()];
		parameters = new Hashtable<String, Parameter>();
		for (int i = 0; i < params2.size(); i++) {
			String param = params2.get(i);
			this.params[i] = param;
			parameters.put(param, new Parameter(new Untyped()));
		}
	}

	public void setNext(boolean next) {
		this.next = next;
	}

	public MyType getType() {
		return type;
	}

	public void setType(MyType type) {
		this.type = type;
	}

	public String toString() {
		String s = "[Name: " + name + ", Type: " + type + ", Params: ";
		Enumeration<Parameter> e = parameters.elements();
		while (e.hasMoreElements()) {
			Parameter v = e.nextElement();
			s += v + ",";

		}
		s += "]";
		return s;
	}

	public void setEquation(boolean isEquation) {
		this.isEquation = isEquation;
	}

	public boolean isEquation() {
		return isEquation;
	}

	public void setTemporal(boolean temporal) {
		this.temporal = temporal;
	}

	public boolean isTemporal() {
		return temporal;
	}

}
