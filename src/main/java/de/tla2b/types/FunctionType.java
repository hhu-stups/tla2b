package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class FunctionType extends AbstractHasFollowers {
	private TLAType domain;
	private TLAType range;

	public FunctionType(TLAType domain, TLAType range) {
		super(FUNCTION);
		this.setDomain(domain);
		this.setRange(range);
	}

	public FunctionType() {
		super(FUNCTION);
		this.setDomain(new Untyped());
		this.setRange(new Untyped());
	}

	@Override
	public String toString() {
		String res = "POW(" + domain + "*";
		if (range instanceof TupleType) {
			res += "(" + range + ")";
		} else{
			res += range;
		}
		res += ")";
		return res;
	}

	public void update(TLAType oldType, TLAType newType) {
		if (domain == oldType)
			setDomain(newType);
		if (range == oldType)
			setRange(newType);
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof FunctionType) {
			FunctionType f = (FunctionType) o;
			return domain.compare(f.domain) && range.compare(f.range);
		}
		if(o instanceof TupleType){
			return o.compare(this);
		}

		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		return domain.equals(o) || domain.contains(o) || range.equals(o)
				|| range.contains(o);
	}

	@Override
	public boolean isUntyped() {
		return domain.isUntyped() || range.isUntyped();
	}

	@Override
	public TLAType cloneTLAType() {
		return new FunctionType(domain.cloneTLAType(), range.cloneTLAType());
	}

	@Override
	public FunctionType unify(TLAType o) throws UnificationException {
		if (!this.compare(o))
			throw new UnificationException();
		if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		}
		if (o instanceof FunctionType) {
			domain = domain.unify(((FunctionType) o).domain);
			range = range.unify(((FunctionType) o).range);
			return this;
		}
		if (o instanceof TupleType){
			return (FunctionType) o.unify(this);
		}
		throw new RuntimeException();
	}

	public TLAType getDomain() {
		return domain;
	}

	public TLAType getRange() {
		return range;
	}

	public void setDomain(TLAType domain) {
		this.domain = domain;
		if (domain instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) domain).addFollower(this);
		}
	}

	public void setRange(TLAType range) {
		this.range = range;
		if (range instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) range).addFollower(this);
		}
	}

}
