package types;

import exceptions.UnificationException;

public class IntType extends BType {

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
	public boolean compare(BType o) {
		if (o.getKind() == UNTYPED || o.getKind() == INTEGER)
			return true;
		else
			return false;
	}

	@Override
	public IntType unify(BType o) throws UnificationException {
		if (o.getKind() == INTEGER) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public IntType cloneBType() {
		return this;
	}
	
	@Override
	public boolean contains(BType o) {
		return false;
	}
}