package types;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import exceptions.UnificationException;

public class StructType extends AbstractHasFollowers {
	private ArrayList<String> fields;
	private Hashtable<String, BType> types;
	private boolean hasOrderedFields;

	public StructType() {
		super(STRUCT);
		hasOrderedFields = false;
		fields = new ArrayList<String>();
		types = new Hashtable<String, BType>();
	}

	
	public void setHasOrderedFields(){
		hasOrderedFields = true;
	}
	
	

	public BType getType(String field) {
		return types.get(field);
	}

	public void add(String name, BType type) {
		fields.add(name);
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
				types.put(key, New);
				if (New instanceof AbstractHasFollowers) {
					// set new reference
					((AbstractHasFollowers) New).addFollower(this);
				}
			}
		}
	}

	@Override
	public String toString() {
		if (hasOrderedFields) {
			String res = "struct(";
			for (int i = 0; i < fields.size(); i++) {
				String field = fields.get(i);
				res += field + ":" + types.get(field);
				if (i < fields.size() - 1) {
					res += ",";
				}
			}
			res += ")";
			return res;
		} else {
			String res = "struct(";
			Enumeration<String> keys = this.types.keys();
			while (keys.hasMoreElements()){
				String field = keys.nextElement();
				res+= field + ":" + this.types.get(field);
					res+=",";
			}
			res += "...)";
			return res;
		}

	}

	@Override
	public boolean isUntyped() {
		if (!hasOrderedFields) {
			return true;
		}
		for (int i = 0; i < fields.size(); i++) {
			String field = fields.get(i);
			if (types.get(field).isUntyped())
				return true;
		}
		return false;
	}

	@Override
	public boolean compare(BType o) {
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof StructType) {
			StructType s = (StructType) o;

			// both have ordered fields
			if (this.hasOrderedFields && s.hasOrderedFields) {
				if (this.fields.size() != s.fields.size()) {
					return false;
				}
				for (int i = 0; i < fields.size(); i++) {
					String thisField = this.fields.get(i);
					String thatField = s.fields.get(i);
					if (!thisField.equals(thatField)
							|| !this.types.get(thisField).compare(
									s.types.get(thatField))) {
						return false;
					}
				}
				return true;
			}

			// both have not ordered fields
			if (!this.hasOrderedFields && !s.hasOrderedFields) {
				Enumeration<String> keys = this.types.keys();
				while (keys.hasMoreElements()) {
					String field = keys.nextElement();
					if (s.types.containsKey(field)) {
						if (!this.types.get(field).compare(s.types.get(field))) {
							return false;
						}
					}
				}
				return true;
			}

			// this has ordered fields, s has not
			if (this.hasOrderedFields && !s.hasOrderedFields) {
				Enumeration<String> e = s.types.keys();
				while (e.hasMoreElements()) {
					String thatField = e.nextElement();
					if (this.types.containsKey(thatField)) {
						if (!this.types.get(thatField).compare(
								s.types.get(thatField))) {
							return false;
						}
					} else {
						// this has no field 'thatField'
						return false;
					}
				}
				return true;
			}
			// s has ordered fields, this has not
			if (!this.hasOrderedFields && s.hasOrderedFields) {
				return s.compare(this);
			}

		}
		// s is no struct type and no untyped
		return false;
	}

	@Override
	public StructType unify(BType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof StructType) {
			StructType s = (StructType) o;

			// both have ordered fields
			if (this.hasOrderedFields && s.hasOrderedFields) {
				for (int i = 0; i < this.fields.size(); i++) {
					String field = this.fields.get(i);
					BType res = this.types.get(field).unify(s.types.get(field));
					this.types.put(field, res);
				}
				return this;
			}

			// both have not ordered fields
			if (!this.hasOrderedFields && !s.hasOrderedFields) {
				Enumeration<String> keys = s.types.keys();
				while (keys.hasMoreElements()) {
					String field = keys.nextElement();
					if (this.types.containsKey(field)) {
						BType res = this.types.get(field).unify(
								s.types.get(field));
						this.types.put(field, res);
					} else {
						BType t = s.types.get(field);
						this.types.put(field, t);
						if (t instanceof AbstractHasFollowers) {
							((AbstractHasFollowers) t).addFollower(this);
						}
					}
				}
				return this;
			}

			// this has ordered fields, s has not
			if (this.hasOrderedFields && !s.hasOrderedFields) {
				Enumeration<String> keys = s.types.keys();
				while (keys.hasMoreElements()) {
					String field = keys.nextElement();
					BType res = this.types.get(field).unify(s.types.get(field));
					this.types.put(field, res);
				}
				return this;
			}

			// s has ordered fields, this has not
			if (!this.hasOrderedFields && s.hasOrderedFields) {
				return s.unify(this);
			}
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
		
		clone.hasOrderedFields = this.hasOrderedFields;
		return clone;
	}
	
	public ArrayList<String> getFields(){
		return new ArrayList<String>(fields);
	}
}
