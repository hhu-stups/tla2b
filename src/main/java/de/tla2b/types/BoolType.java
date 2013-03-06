package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class BoolType extends TLAType {

	private static BoolType instance = new BoolType();

	private BoolType() {
		super(BOOL);
	}

	public static BoolType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "BOOL";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == BOOL)
			return true;
		else
			return false;
	}
	
	@Override
	public BoolType unify(TLAType o) throws UnificationException {
		if (o.getKind() == BOOL) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public BoolType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		return false;
	}
}