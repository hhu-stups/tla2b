/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.config;

import de.tla2b.types.TLAType;
import tlc2.value.Value;

public class ValueObj {
	private Value value;
	private TLAType type;

	public ValueObj(Value value, TLAType t) {
		this.value = value;
		this.type = t;
	}

	public Value getValue() {
		return value;
	}

	public void setValue(Value value) {
		this.value = value;
	}

	public void setType(TLAType type) {
		this.type = type;
	}
	
	public TLAType getType(){
		return type;
	}
		
}
