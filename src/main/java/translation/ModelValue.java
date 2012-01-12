/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import types.BType;

public class ModelValue {
	private String name;
	private BType type;
	public ModelValue(String name, BType t){
		this.name = name;
		this.type = t;
	}
	
	public ModelValue(String name){
		this.name = name;
	}

	public BType getType(){
		return type;
	}

	public String getName(){
		return name;
	}
	
	@Override
	public boolean equals(Object o){
		if(o instanceof ModelValue){
			ModelValue o2 = (ModelValue)o;
			if(this.name.equals(o2.name)){
				return true;
			}else{
				return false;
			}
		}else{
			return false;
		}
	}
}
