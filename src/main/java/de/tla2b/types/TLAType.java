package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;


public abstract class TLAType implements IType {
	private int kind;

	public TLAType(int t) {
		this.kind = t;
	}

	public final int getKind() {
		return kind;
	}

	public abstract String toString();

	public abstract boolean compare(TLAType o);
	
	public abstract boolean contains(TLAType o);
	
	public abstract boolean isUntyped();
	
	public abstract TLAType cloneTLAType();

	public abstract TLAType unify(TLAType o) throws UnificationException;
	
	public TLAType unityAll(TLAType[] types) throws UnificationException{
		TLAType current = this;
		for (int i = 0; i < types.length; i++) {
			current = current.unify(types[i]);
		}
		return current;
	}

	public final String printObjectToString() {
		return super.toString();
	}

}
