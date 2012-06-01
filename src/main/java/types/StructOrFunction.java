/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package types;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.Map.Entry;

import exceptions.UnificationException;

public class StructOrFunction extends AbstractHasFollowers {
	private LinkedHashMap<String, BType> types;

	public StructOrFunction(String name, BType type) {
		super(STRUCT_OR_FUNCTION);
		types = new LinkedHashMap<String, BType>();
		types.put(name, type);
	}

	public StructOrFunction() {
		super(STRUCT_OR_FUNCTION);
		types = new LinkedHashMap<String, BType>();
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
		testRecord();
	}

	@Override
	public String toString() {
		String res = "StructOrFunction(";
		for (Iterator<String> keys = types.keySet().iterator(); keys.hasNext();) {
			String key = keys.next();
			res += "\""+key + "\" : " + types.get(key);
			if (keys.hasNext())
				res += ", ";
		}
		res += ")";
		return res;
	}

	@Override
	public boolean compare(BType o) {
		if (this.contains(o) || o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof StructType) {
			StructType s = (StructType) o;
			Iterator<String> thisKeys = types.keySet().iterator();
			while (thisKeys.hasNext()) {
				String fieldName = (String) thisKeys.next();
				if (s.getFields().contains(fieldName)) {
					if (!this.types.get(fieldName)
							.compare(s.getType(fieldName))) {
						return false;
					}
				}
			}
			return true;
		}
		if (o instanceof PowerSetType) {
			PowerSetType p = (PowerSetType) o;
			BType sub = p.getSubType();
			if (sub.getKind() == UNTYPED)
				return true;

			if (sub instanceof PairType) {
				PairType pair = (PairType) sub;
				if (pair.getFirst().compare(StringType.getInstance())) {
					for (String key : types.keySet()) {
						if (!pair.getSecond().compare(types.get(key)))
							return false;
					}
					return true;
				} else
					return false;
			} else
				return false;
		}

		if (o instanceof StructOrFunction) {
			StructOrFunction s = (StructOrFunction) o;

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

	@Override
	public boolean contains(BType o) {
		Iterator<String> thisKeys = types.keySet().iterator();
		while (thisKeys.hasNext()) {
			String fieldName = (String) thisKeys.next();
			BType type = this.types.get(fieldName);
			if (type.equals(o) || type.contains(o))
				return true;
		}
		return false;
	}

	@Override
	public boolean isUntyped() {
		return true;
		// Iterator<BType> itr = types.values().iterator();
		// while (itr.hasNext()) {
		// if (itr.next().isUntyped())
		// return true;
		// }
		// return false;
	}

	@Override
	public BType cloneBType() {
		StructOrFunction res = new StructOrFunction();
		for (String field : types.keySet()) {
			res.types.put(field, this.types.get(field));
		}
		return res;
	}

	@Override
	public BType unify(BType o) throws UnificationException {
		if (!this.compare(o))
			throw new UnificationException();

		if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		}

		if (o instanceof PowerSetType) {
			Iterator<BType> itr = types.values().iterator();
			BType temp = itr.next();
			while (itr.hasNext()) {
				temp = temp.unify(itr.next());
			}
			PowerSetType found = new PowerSetType(new PairType(
					StringType.getInstance(), temp));
			return found.unify(o);
		}
		if (o instanceof StructType) {
			StructType res = new StructType();

			for (String field : types.keySet()) {
				res.add(field, this.types.get(field));
			}
			return o.unify(res);
		}
		if (o instanceof StructOrFunction) {
			StructOrFunction other = (StructOrFunction) o;
			for (String field : other.types.keySet()) {
				BType type = other.types.get(field);
				if (this.types.containsKey(field)) {
					BType res = this.types.get(field).unify(type);
					this.types.put(field, res);
				} else {
					if (type instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) type).addFollower(this);
					}
					this.types.put(field, type);
				}
			}
			BType res = testRecord();
			return res;
		}
		return this;
	}

	private BType testRecord() {
		Iterator<BType> itr = types.values().iterator();
		BType temp = itr.next().cloneBType();
		while (itr.hasNext()) {
			BType next = itr.next().cloneBType();
			try {
				temp.unify(next);
			} catch (UnificationException e) {
				StructType res = new StructType();
				for (String field : this.types.keySet()) {
					res.add(field, this.types.get(field));
				}
				this.setFollowersTo(res);
				return res;
			}
		}
		return this;
	}

	public PowerSetType getFunction() {
		Iterator<BType> itr = types.values().iterator();
		return new PowerSetType(new PairType(StringType.getInstance(),
				itr.next()));
	}

}
