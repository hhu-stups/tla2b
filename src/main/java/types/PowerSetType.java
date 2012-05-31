package types;

import exceptions.UnificationException;

public class PowerSetType extends AbstractHasFollowers {
	private BType subType;

	public PowerSetType(BType t) {
		super(POW);
		setSubType(t);
	}

	public BType getSubType() {
		return subType;
	}

	public void setSubType(BType t) {
		// if (subType instanceof AbstractHasFollowers) {
		// // delete old reference
		// ((AbstractHasFollowers) subType).deleteFollower(this);
		// }

		if (t instanceof AbstractHasFollowers) {
			// set new reference
			((AbstractHasFollowers) t).addFollower(this);
		}
		this.subType = t;

		// setting subType can lead to a completely typed type
		if (!this.isUntyped()) {
			// this type is completely typed
			this.deleteFollowers();
		}
	}

	public PowerSetType unify(BType o) throws UnificationException {

		if (!this.compare(o)|| this.contains(o)) {
			throw new UnificationException();
		}
		// if o has followers than switch pointer to this
		if (o instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) o).setFollowersTo(this);
		}
		
		if (o instanceof StructOrFunction){
			return (PowerSetType)o.unify(this);
		}
		if (o instanceof PowerSetType) {
			PowerSetType p = (PowerSetType) o;
			this.subType = this.subType.unify(p.subType);

//			if (this.subType instanceof AbstractHasFollowers) {
//				((AbstractHasFollowers) this.subType).removeFollower(o);
//			}
		}
		return this;
	}

	@Override
	public boolean compare(BType o) {
		if(this.contains(o))
			return false;
		
		if (o.getKind() == UNTYPED)
			return true;
		
		if (o instanceof StructOrFunction){
			return o.compare(this);
		}

		if (o instanceof PowerSetType) {
			PowerSetType p = (PowerSetType) o;
			// test sub types compatibility
			return this.subType.compare(p.subType);
		} else
			return false;
	}

	@Override
	public String toString() {
		String res = "POW(" + this.getSubType() + ")";

		return res;
	}

	@Override
	public boolean isUntyped() {
		return subType.isUntyped();
	}

	@Override
	public PowerSetType cloneBType() {
		return new PowerSetType(this.subType.cloneBType());
	}


	@Override
	public boolean contains(BType o) {
		return this.getSubType().equals(o) || this.getSubType().contains(o);
	}

}
