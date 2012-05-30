package types;

import exceptions.UnificationException;

public class ModelValueType extends BType {

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
	public boolean compare(BType o) {
		if (o.getKind() == UNTYPED || o.getKind() == MODELVALUE)
			return true;
		else
			return false;
	}
	
	@Override
	public ModelValueType unify(BType o) throws UnificationException {
		if (o.getKind() == MODELVALUE) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public ModelValueType cloneBType() {
		return this;
	}
	
	@Override
	public boolean contains(BType o) {
		return false;
	}
}