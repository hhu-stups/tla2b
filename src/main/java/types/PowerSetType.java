package types;

public class PowerSetType extends MyType {
	private MyType subType;

	public PowerSetType(MyType t) {
		super(POW);
		setSubType(t);
	}

	public MyType getSubType() {
		return subType;
	}

	public void setSubType(MyType t) {
		subType = t;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		try {
			MyType t2 = (MyType) o;
			if (this.getType() == UNTYPED || t2.getType() == UNTYPED) {
				return true;
			}

			PowerSetType s2 = (PowerSetType) o;
			if (this.getSubType().equals(s2.getSubType())) {
				return true;
			} else
				return false;

		} catch (ClassCastException e) {
			return false;
		}
	}

	public String toString() {
		if(subType.getType()== PAIR){
			return "POW"+subType;
		}
		else return "POW(" + subType + ")";
	}

	@Override
	public boolean isUntyped() {
		return this.getSubType().isUntyped();
	}

	public MyType compare(MyType o) {
		if (!this.equals(o))
			return null;
		
		if(this.getType() == UNTYPED)
			return o;
		if(o.getType() == UNTYPED)
			return this;
		
		
		if (this.isUntyped() || o.isUntyped()) {
			return new PowerSetType(subType.compare(((PowerSetType) o).subType));

		} else
			return this;

	}
}
