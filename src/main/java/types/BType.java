package types;

import exceptions.UnificationException;


public abstract class BType implements IType {
	private int kind;

	public BType(int t) {
		this.kind = t;
	}

	public final int getKind() {
		return kind;
	}

	public abstract String toString();

	public abstract boolean compare(BType o);
	
	public abstract boolean isUntyped();
	
	public abstract BType cloneBType();

	public abstract BType unify(BType o) throws UnificationException;
	
	public BType unityAll(BType[] types) throws UnificationException{
		BType current = this;
		for (int i = 0; i < types.length; i++) {
			current = current.unify(types[i]);
		}
		return current;
	}

	public final String printObjectToString() {
		return super.toString();
	}

}
