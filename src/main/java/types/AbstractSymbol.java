package types;

public abstract class AbstractSymbol {

	private BType type;
	
	public AbstractSymbol(BType t){
		setType(t);
	}
	
	public BType getType() {
		return type;
	}


	protected void setType(BType t) {
		this.type = t;
		if (type instanceof AbstractHasFollowers) {
			AbstractHasFollowers p = (AbstractHasFollowers) t;
			p.addFollower(this);
		}
	}
}
