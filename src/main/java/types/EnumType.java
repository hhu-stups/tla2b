/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package types;

import java.util.ArrayList;
import java.util.LinkedHashSet;

import exceptions.UnificationException;

public class EnumType extends AbstractHasFollowers {
	public LinkedHashSet<String> modelvalues;
	public int id;
	
	public EnumType(ArrayList<String> enums) {
		super(MODELVALUE);
		modelvalues = new LinkedHashSet<String>(enums);
	}

	@Override
	public String toString() {
		return "ENUM"+id;
	}

	public LinkedHashSet<String> getValues(){
		return modelvalues;
	}
	@Override
	public boolean isUntyped() {
		return false;
	}
	
	@Override
	public boolean compare(BType o) {
		if (o.getKind() == UNTYPED || o.getKind() == MODELVALUE)
			return true;
		else
			return false;
	}
	
	@Override
	public EnumType unify(BType o) throws UnificationException {
		if (o instanceof EnumType) {
			this.modelvalues.addAll(((EnumType)o).modelvalues);
			((EnumType) o).setFollowersTo(this);
			return this;
		} else if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public EnumType cloneBType() {
		return this;
	}
}