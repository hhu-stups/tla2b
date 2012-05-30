package types;

import exceptions.UnificationException;

public class PairType extends AbstractHasFollowers {

	private BType first;
	private BType second;

	public PairType() {
		super(PAIR);
		setFirst(new Untyped());
		setSecond(new Untyped());
	}

	public PairType(BType f, BType s) {
		super(PAIR);
		this.first = f;
		if (first instanceof AbstractHasFollowers) {
			AbstractHasFollowers firstHasFollowers = (AbstractHasFollowers) first;
			firstHasFollowers.addFollower(this);
		}
		this.second = s;
		if (second instanceof AbstractHasFollowers) {
			AbstractHasFollowers secondHasFollowers = (AbstractHasFollowers) second;
			secondHasFollowers.addFollower(this);
		}
	}

	public BType getFirst() {
		return first;
	}

	public void setFirst(BType f) {
		this.first = f;

		if (first instanceof AbstractHasFollowers) {
			AbstractHasFollowers firstHasFollowers = (AbstractHasFollowers) first;
			firstHasFollowers.addFollower(this);
		}

		// setting first can leads to a completely typed type
		if (!this.isUntyped()) {
			// this type is completely typed
			this.deleteFollowers();
		}
	}

	public BType getSecond() {
		return second;
	}

	public void setSecond(BType s) {
		this.second = s;

		if (second instanceof AbstractHasFollowers) {
			AbstractHasFollowers secondHasFollowers = (AbstractHasFollowers) second;
			secondHasFollowers.addFollower(this);
		}

		// setting second can leads to a completely typed type
		if (!this.isUntyped()) {
			// this type is completely typed
			this.deleteFollowers();
		}
	}

	@Override
	public String toString() {
		String res = first + "*";
		if (second instanceof PairType) {
			res += "(" + second + ")";
		} else
			res += second;
		return res;
	}

	@Override
	public boolean isUntyped() {
		return first.isUntyped() || second.isUntyped();
	}

	@Override
	public PairType unify(BType o) throws UnificationException {
		if (!this.compare(o))
			throw new UnificationException();
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof PairType) {
			PairType p = (PairType) o;
			this.first = this.first.unify(p.first);
			this.second = this.second.unify(p.second);
		}
		return this;
	}

	@Override
	public boolean compare(BType o) {
		if (this.contains(o))
			return false;
		if (o.getKind() == UNTYPED)
			return true;

		if (o instanceof PairType) {
			PairType p = (PairType) o;
			// test first and second component compatibility
			return this.first.compare(p.first) && this.second.compare(p.second);
		} else
			return false;
	}

	@Override
	public PairType cloneBType() {
		return new PairType(this.first.cloneBType(), this.second.cloneBType());
	}

	@Override
	public boolean contains(BType o) {
		return first.equals(o) || first.contains(o) || second.equals(o)
				|| second.contains(o);
	}

}
