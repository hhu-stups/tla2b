package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class PairType extends AbstractHasFollowers {

	private TLAType first;
	private TLAType second;

	public PairType() {
		super(PAIR);
		setFirst(new Untyped());
		setSecond(new Untyped());
	}

	public PairType(TLAType f, TLAType s) {
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

	public TLAType getFirst() {
		return first;
	}

	public void setFirst(TLAType f) {
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

	public TLAType getSecond() {
		return second;
	}

	public void setSecond(TLAType s) {
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
	public PairType unify(TLAType o) throws UnificationException {
		if (!this.compare(o))
			throw new UnificationException();
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof PairType) {
			PairType p = (PairType) o;
			this.first = this.first.unify(p.first);
			this.second = this.second.unify(p.second);
			return this;
		}
		throw new RuntimeException();
	}

	@Override
	public boolean compare(TLAType o) {
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
	public PairType cloneTLAType() {
		return new PairType(this.first.cloneTLAType(), this.second.cloneTLAType());
	}

	@Override
	public boolean contains(TLAType o) {
		return first.equals(o) || first.contains(o) || second.equals(o)
				|| second.contains(o);
	}

}
