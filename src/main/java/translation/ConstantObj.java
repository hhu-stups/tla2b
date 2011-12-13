package translation;

import types.BType;


public class ConstantObj {

	private String value;
	private BType type;

	public ConstantObj(String value, BType t) {
		this.value = value;
		this.type = t;
	}

	public String getValue() {
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
