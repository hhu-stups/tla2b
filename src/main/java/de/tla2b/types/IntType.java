package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class IntType extends TLAType {

	private static IntType instance = new IntType();

	private IntType() {
		super(INTEGER);
	}

	public static IntType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "INTEGER";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == INTEGER)
			return true;
		else
			return false;
	}

	@Override
	public IntType unify(TLAType o) throws UnificationException {
		if (o.getKind() == INTEGER) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public IntType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		return false;
	}
}