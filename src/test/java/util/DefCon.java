/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package util;

import java.util.Hashtable;

import types.BType;

public class DefCon {

	public Hashtable<String, BType> parameters;
	protected BType type;
	
	public DefCon(BType t){
		parameters = new Hashtable<String, BType>();
		type = t;
	}

	public BType getType() {
		return type;
	}

	public void setType(BType type) {
		this.type = type;
	}
}
