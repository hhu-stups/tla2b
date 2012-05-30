package types;

import exceptions.UnificationException;

public class Untyped extends AbstractHasFollowers {

	public Untyped() {
		super(UNTYPED);
	}

	public BType unify(BType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		// u2 contains more or equal type information than untyped (this)
		this.setFollowersTo(o);
		//this.deleteFollowers();
		return o;
	}
	
	@Override
	public boolean compare(BType o){
		if(o.contains(this)){
			return false;
		}
		return true;
	}
	
	@Override
	public boolean contains(BType o){
		return false;
	}

	@Override
	public String toString() {
		return "UNTYPED_"+hashCode();
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

	@Override
	public Untyped cloneBType() {
		return new Untyped();
	}
}
