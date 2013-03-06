package de.tla2b.types;

public abstract class AbstractSymbol {

	private TLAType type;
	
	public AbstractSymbol(TLAType t){
		setType(t);
	}
	
	public TLAType getType() {
		return type;
	}


	protected void setType(TLAType t) {
		this.type = t;
		if (type instanceof AbstractHasFollowers) {
			AbstractHasFollowers p = (AbstractHasFollowers) t;
			p.addFollower(this);
		}
	}
}
