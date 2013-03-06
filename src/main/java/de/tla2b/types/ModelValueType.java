package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class ModelValueType extends TLAType {

	private static ModelValueType instance = new ModelValueType();

	private ModelValueType() {
		super(MODELVALUE);
	}

	public static ModelValueType getInstance() {
		return instance;
	}


	@Override
	public String toString() {
		return "ENUM";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}
	
	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == MODELVALUE)
			return true;
		else
			return false;
	}
	
	@Override
	public ModelValueType unify(TLAType o) throws UnificationException {
		if (o.getKind() == MODELVALUE) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public ModelValueType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		return false;
	}
}