/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.types;

import java.util.ArrayList;
import java.util.LinkedHashSet;

import de.tla2b.exceptions.UnificationException;



public class EnumType extends AbstractHasFollowers {
	public LinkedHashSet<String> modelvalues;
	public int id;
	private boolean noVal = false;

	public EnumType(ArrayList<String> enums) {
		super(MODELVALUE);
		modelvalues = new LinkedHashSet<String>(enums);
	}

	public void setNoVal() {
		noVal = true;
	}

	public boolean hasNoVal() {
		return noVal;
	}

	@Override
	public String toString() {
		return "ENUM" + id;
	}

	public LinkedHashSet<String> getValues() {
		return modelvalues;
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == MODELVALUE)
			return true;
		else
			return false;
	}

	@Override
	public EnumType unify(TLAType o) throws UnificationException {
		if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		}
		if (o instanceof EnumType) {
			EnumType e = (EnumType) o;
			e.setFollowersTo(this);
			this.modelvalues.addAll(((EnumType) o).modelvalues);
			return this;
		}
		throw new UnificationException();
	}

	@Override
	public EnumType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		//TODO is this really false
		return false;
	}
}