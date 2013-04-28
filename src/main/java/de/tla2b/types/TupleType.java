package de.tla2b.types;

import java.util.ArrayList;

import de.tla2b.exceptions.UnificationException;

public class TupleType extends AbstractHasFollowers {
	private ArrayList<TLAType> types;

	public TupleType(ArrayList<TLAType> typeList) {
		super(TUPLE);
		setTypes(typeList);
	}

	public TupleType(int size) {
		super(TUPLE);
		ArrayList<TLAType> list = new ArrayList<TLAType>();
		for (int i = 0; i < size; i++) {
			list.add(new Untyped());
		}
		setTypes(list);
	}

	public ArrayList<TLAType> getTypes() {
		return new ArrayList<TLAType>(types);
	}

	public void setTypes(ArrayList<TLAType> types) {
		this.types = types;
		types = new ArrayList<TLAType>(types);
		for (TLAType tlaType : types) {
			if (tlaType instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) tlaType).addFollower(this);
			}
		}
	}

	@Override
	public String toString() {
		String res = "";
		for (int i = 0; i < types.size(); i++) {
			if (types.get(i) instanceof TupleType && i != 0) {
				res += "(" + types.get(i) + ")";
			} else
				res += types.get(i);

			if (i < types.size() - 1) {
				res += "*";
			}
		}
		return res;
	}

	public void update(TLAType oldType, TLAType newType) {
		for (int i = 0; i < types.size(); i++) {
			TLAType t = types.get(i);
			if (oldType == t) {
				types.set(i, newType);
			}
		}
		if (oldType instanceof AbstractHasFollowers)
			((AbstractHasFollowers) oldType).addFollower(this);
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof TupleType) {
			TupleType t = (TupleType) o;
			if (this.types.size() != t.types.size()) {
				for (int i = 0; i < t.types.size(); i++) {
					if (!compareToAll(t.types.get(i))) {
						return false;
					}
				}
				// both are sequences with different lengths
				return true;
			}
			for (int i = 0; i < types.size(); i++) {
				if (!types.get(i).compare(t.types.get(i)))
					return false;
			}
			return true;
		}
		if (o instanceof FunctionType) {
			//TODO
			FunctionType func = (FunctionType) o;
			if (!(func.getDomain() instanceof IntType)) {
				return false;
			}
			TLAType range = func.getRange();
			for (int i = 0; i < types.size(); i++) {
				if (types.get(i).compare(range)) {
					continue;
				} else {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	private boolean compareToAll(TLAType other) {
		for (int i = 0; i < types.size(); i++) {
			for (int j = i + 1; j < types.size(); j++) {
				if (!types.get(i).compare(types.get(j)))
					return false;
			}
			if (!types.get(i).compare(other))
				return false;
		}
		return true;
	}

	@Override
	public boolean contains(TLAType o) {
		for (TLAType tlaType : types) {
			if (tlaType.equals(o) || tlaType.contains(o))
				return true;
		}
		return false;
	}

	@Override
	public boolean isUntyped() {
		for (TLAType tlaType : types) {
			if (tlaType.isUntyped())
				return true;
		}
		return false;
	}

	@Override
	public TLAType cloneTLAType() {
		ArrayList<TLAType> list = new ArrayList<TLAType>();
		for (TLAType tlaType : types) {
			list.add(tlaType.cloneTLAType());
		}
		return new TupleType(list);
	}

	@Override
	public TLAType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof Untyped) {
			((Untyped) o).setFollowersTo(this);
			return this;
		}
		if (o instanceof TupleType) {
			TupleType tuple = (TupleType) o;
			if (this.types.size() != tuple.types.size()) {
				TLAType t = types.get(0);
				for (int i = 1; i < types.size(); i++) {
					t = t.unify(types.get(i));
				}
				for (int i = 0; i < tuple.types.size(); i++) {
					t = t.unify(tuple.types.get(i));
				}
				return new FunctionType(IntType.getInstance(), t);
			} else {
				for (int i = 0; i < types.size(); i++) {
					TLAType res = types.get(i).unify(tuple.types.get(i));
					types.set(i, res);
					if (res instanceof AbstractHasFollowers)
						((AbstractHasFollowers) res).addFollower(this);
				}
				return this;
			}
		}
		if (o instanceof FunctionType) {
			//TODO
			if(compareToAll(new Untyped())){
				//Function 
				TLAType t = types.get(0);
				for (int i = 1; i < types.size(); i++) {
					t = t.unify(types.get(i));
				}
				FunctionType func = new FunctionType(IntType.getInstance(), t);
				this.setFollowersTo(func);
				return func.unify(o);
			}else{
				TLAType res = types.get(1).unify(((FunctionType) o).getRange());
				types.set(1, res);
				return this;
			}
			
		}
		throw new RuntimeException();
	}

}
