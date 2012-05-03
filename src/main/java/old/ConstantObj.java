package old;

import tlc2.value.Value;
import types.BType;


public class ConstantObj {

	private Object value;
	private BType type;

	public ConstantObj(Object value, BType t) {
		this.value = value;
		this.type = t;
	}

	public Object getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public void setType(BType type) {
		this.type = type;
	}
	
	public BType getType(){
		return type;
	}

}
