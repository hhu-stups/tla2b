package translation;

import types.MyType;

public class Parameter {
	private MyType type;
	private ExprReturn er;
	
	public boolean hasValue(){
		if (er==null) return false;
		else return true;
	}
	public Parameter(MyType type){
		this.type = type;
		er = null;
	}
	public MyType getType() {
		return type;
	}
	public void setType(MyType type) {
		this.type = type;
	}
	public ExprReturn getEr() {
		return er;
	}
	public void setEr(ExprReturn er) {
		this.er = er;
	}
	public String toString(){
		return "["+type+" : "+ er +"]";
	}
}
