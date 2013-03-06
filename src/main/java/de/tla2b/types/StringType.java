/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.types;

import de.tla2b.exceptions.UnificationException;

public class StringType extends TLAType {

	private static StringType instance = new StringType();

	private StringType() {
		super(STRING);
	}
	
	public static StringType getInstance(){
		return instance;
	}

	@Override
	public String toString() {
		return "STRING";
	}

	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == STRING)
			return true;
		else
			return false;
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public StringType unify(TLAType o) throws UnificationException {
		if (o.getKind() == STRING) {
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			((Untyped) o).deleteFollowers();
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public StringType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		return false;
	}
	
}
