package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class SetType extends AbstractHasFollowers {
	private TLAType subType;

	public SetType(TLAType t) {
		super(POW);
		setSubType(t);
	}

	public TLAType getSubType() {
		return subType;
	}

	public void setSubType(TLAType t) {
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

	public SetType unify(TLAType o) throws UnificationException {

		if (!this.compare(o)|| this.contains(o)) {
			throw new UnificationException();
		}
		// if o has followers than switch pointer to this
		if (o instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) o).setFollowersTo(this);
		}
		
		if (o instanceof StructOrFunction){
			return (SetType)o.unify(this);
		}
		if (o instanceof SetType) {
			SetType p = (SetType) o;
			this.subType = this.subType.unify(p.subType);

//			if (this.subType instanceof AbstractHasFollowers) {
//				((AbstractHasFollowers) this.subType).removeFollower(p);
//			}
		}
		return this;
	}

	@Override
	public boolean compare(TLAType o) {
		if(this.contains(o))
			return false;
		
		if (o.getKind() == UNTYPED)
			return true;
		
		if (o instanceof StructOrFunction){
			return o.compare(this);
		}

		if (o instanceof SetType) {
			SetType p = (SetType) o;
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
	public SetType cloneTLAType() {
		return new SetType(this.subType.cloneTLAType());
	}


	@Override
	public boolean contains(TLAType o) {
		return this.getSubType().equals(o) || this.getSubType().contains(o);
	}

}
