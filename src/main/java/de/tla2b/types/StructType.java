package de.tla2b.types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import de.tla2b.exceptions.UnificationException;



public class StructType extends AbstractHasFollowers {
	private LinkedHashMap<String, TLAType> types;

	public StructType() {
		super(STRUCT);
		types = new LinkedHashMap<String, TLAType>();
	}

	public TLAType getType(String fieldName) {
		return types.get(fieldName);
	}

	public void add(String name, TLAType type) {
		if (type instanceof AbstractHasFollowers) {
			// set new reference
			((AbstractHasFollowers) type).addFollower(this);
		}
		types.put(name, type);
	}

	public void setNewType(TLAType old, TLAType New) {
		Set<Entry<String, TLAType>> set = types.entrySet();
		Iterator<Entry<String, TLAType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, TLAType> entry = iterator.next();
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
		if(!keys.hasNext())
			res += "...";
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
		Iterator<TLAType> ts = types.values().iterator();
		while (ts.hasNext()) {
			TLAType bType = (TLAType) ts.next();
			if (bType.isUntyped())
				return true;
		}
		return false;
	}

	public boolean compare(TLAType o) {
		if(this.contains(o)|| o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		
		if (o instanceof StructOrFunction){
			return o.compare(this);
		}
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
			return true;
		}
		return false;
	}

	public StructType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof StructOrFunction){
			return (StructType) o.unify(this);
		}
		
		if (o instanceof StructType) {
			StructType s = (StructType) o;
			Iterator<String> keys = s.types.keySet().iterator();
			while (keys.hasNext()) {
				String fieldName = (String) keys.next();
				TLAType sType = s.types.get(fieldName);
				if (this.types.containsKey(fieldName)) {
					TLAType res = this.types.get(fieldName).unify(sType);
					this.types.put(fieldName, res);
				} else {
					if (sType instanceof AbstractHasFollowers) {
						// set new reference
						((AbstractHasFollowers) sType).addFollower(this);
					}
					this.types.put(fieldName, sType);
				}
			}
			return this;
		}
		return this;
	}

	@Override
	public StructType cloneTLAType() {
		StructType clone = new StructType();

		Set<Entry<String, TLAType>> set = this.types.entrySet();
		Iterator<Entry<String, TLAType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, TLAType> entry = iterator.next();
			String field = entry.getKey();
			TLAType type = entry.getValue().cloneTLAType();
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
	public boolean contains(TLAType o) {
		Iterator<TLAType> ts = types.values().iterator();
		while (ts.hasNext()) {
			TLAType bType = (TLAType) ts.next();
			if (bType.equals(o) || bType.contains(o))
				return true;
		}
		return false;
	}
}
