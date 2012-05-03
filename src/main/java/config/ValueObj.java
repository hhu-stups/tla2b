/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package config;

import tlc2.value.Value;
import types.BType;

public class ValueObj {
	private Value value;
	private BType type;

	public ValueObj(Value value, BType t) {
		this.value = value;
		this.type = t;
	}

	public Value getValue() {
		return value;
	}

	public void setValue(Value value) {
		this.value = value;
	}

	public void setType(BType type) {
		this.type = type;
	}
	
	public BType getType(){
		return type;
	}
		
}
