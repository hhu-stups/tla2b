package translation;

import types.MyType;


public class Constant {

	private String name;
	private String value;
	private MyType type;

	public Constant(String n, MyType t, String v) {
		name = n;
		type = t;
		value = v;
	}
	

	@Override
	public String toString() {
		return "Name: " + name + ", Value: " + value + ", Type: " +type;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public void setType(MyType type) {
		this.type = type;
	}
	
	public MyType getType(){
		return type;
	}

}
