package types;

public abstract class MyType implements IType {
	private int type;

	public MyType(int t) {
		this.type = t;
	}

	public int getType() {
		return type;
	}

	public void setType(int t) {
		type = t;
	}

	public boolean isUntyped() {
		if (type == UNTYPED)
			return true;
		else if (type == POW) {
			PowerSetType s = (PowerSetType) this;
			return s.getSubType().isUntyped();
		} else
			return false;
	}

	@Override
	public String toString() {
		return "" + type;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		MyType t;
		try {
			t = (MyType) o;
		} catch (ClassCastException e) {
			return false;
		}

		if (this.getType() == UNTYPED || t.getType() == UNTYPED) {
			return true;
		}
		if (type == t.type) {
			return true;
		} else
			return false;
	}
	
	public MyType compare(MyType o){
		if(!this.equals(o)){
			return null;
		}
		
		if(this.getType()== UNTYPED)
			return o;
		if(o.getType() == UNTYPED)
			return this;
		
		return this;
	}

}
