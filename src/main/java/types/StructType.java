package types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import exceptions.UnificationException;

public class StructType extends AbstractHasFollowers {
	private LinkedHashMap<String, BType> types;

	public StructType() {
		super(STRUCT);
		types = new LinkedHashMap<String, BType>();
	}

	public BType getType(String fieldName) {
		return types.get(fieldName);
	}

	public void add(String name, BType type) {
		if (type instanceof AbstractHasFollowers) {
			// set new reference
			((AbstractHasFollowers) type).addFollower(this);
		}
		types.put(name, type);
	}

	public void setNewType(BType old, BType New) {
		Set<Entry<String, BType>> set = types.entrySet();
		Iterator<Entry<String, BType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, BType> entry = iterator.next();
			if (entry.getValue() == old) {
				String key = entry.getKey();
				if (New instanceof AbstractHasFollowers) {
					// set new reference
					((AbstractHasFollowers) New).addFollower(this);
				}
				types.put(key, New);
			}
		}
	}

	@Override
	public String toString() {
		String res = "struct(";
		Iterator<String> keys = types.keySet().iterator();
		while (keys.hasNext()) {
			String fieldName = (String) keys.next();
			res += fieldName + ":" + types.get(fieldName);
			if (keys.hasNext())
				res += ",";
		}
		res += ")";
		return res;
	}

	@Override
	public boolean isUntyped() {
		Iterator<BType> ts = types.values().iterator();
		while (ts.hasNext()) {
			BType bType = (BType) ts.next();
			if (bType.isUntyped())
				return true;
		}
		return false;
	}

	public boolean compare(BType o) {
		if(this.contains(o)|| o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof StructType) {
			StructType s = (StructType) o;

			Iterator<String> thisKeys = types.keySet().iterator();
			while (thisKeys.hasNext()) {
				String fieldName = (String) thisKeys.next();
				if (s.types.containsKey(fieldName)) {
					if (!this.types.get(fieldName).compare(
							s.types.get(fieldName))) {
						return false;
					}
				}
			}
		}
		return true;
	}

	public StructType unify(BType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof StructType) {
			StructType s = (StructType) o;
			Iterator<String> keys = s.types.keySet().iterator();
			while (keys.hasNext()) {
				String fieldName = (String) keys.next();
				BType sType = s.types.get(fieldName);
				if (this.types.containsKey(fieldName)) {
					BType res = this.types.get(fieldName).unify(sType);
					this.types.put(fieldName, res);
				} else {
					if (sType instanceof AbstractHasFollowers) {
						// set new reference
						((AbstractHasFollowers) sType).addFollower(this);
					}
					this.types.put(fieldName, s.types.get(fieldName));
				}
			}
			return this;
		}
		return this;
	}

	@Override
	public StructType cloneBType() {
		StructType clone = new StructType();

		Set<Entry<String, BType>> set = this.types.entrySet();
		Iterator<Entry<String, BType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, BType> entry = iterator.next();
			String field = entry.getKey();
			BType type = entry.getValue().cloneBType();
			clone.add(field, type);
		}

		return clone;
	}

	public ArrayList<String> getFields() {
		ArrayList<String> fields = new ArrayList<String>();
		Iterator<String> keys = this.types.keySet().iterator();
		while (keys.hasNext()) {
			String fieldName = (String) keys.next();
			fields.add(fieldName);
		}
		return fields;
	}

	@Override
	public boolean contains(BType o) {
		Iterator<BType> ts = types.values().iterator();
		while (ts.hasNext()) {
			BType bType = (BType) ts.next();
			if (bType.equals(o) || bType.contains(o))
				return true;
		}
		return false;
	}
}
