package types;

import java.util.ArrayList;

public class StructType extends MyType implements IType {
	public ArrayList<String> names;
	public ArrayList<MyType> types;

	public StructType() {
		super(STRUCT);
		names = new ArrayList<String>();
		types = new ArrayList<MyType>();
	}
	
	public void add(String name, MyType type){
		names.add(name);
		types.add(type);
	}
	
	@Override
	public String toString() {
		String res = "struct(";
		for (int i = 0; i < names.size(); i++) {
			res += names.get(i) + ":" + types.get(i);
			if (i < names.size() - 1) {
				res += ", ";
			}
		}
		res += ")";
		return res;
	}

	@Override
	public boolean isUntyped() {
		for (int i = 0; i < types.size(); i++) {
			if (types.get(i).isUntyped())
				return true;
		}
		return false;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		try {
			MyType t2 = (MyType) o;
			if (this.getType() == UNTYPED || t2.getType() == UNTYPED)
				return true;

			StructType p = (StructType) o;
			for (int i = 0; i < names.size(); i++) {
				if (!names.get(i).equals(p.names.get(i))
						|| !types.get(i).equals(p.types.get(i)))
					return false;
			}
			return true;
		} catch (Exception e) {
			return false;
		}
	}
	
	public MyType compare(MyType o){
		if (!this.equals(o))
			return null;
		
		if(this.getType() == UNTYPED)
			return o;
		if(o.getType() == UNTYPED)
			return this;
		
		
		if (this.isUntyped() || o.isUntyped()) {
			StructType res = new StructType();
			StructType o2 = (StructType) o;
			for (int i = 0; i < types.size(); i++) {
				MyType t =this.types.get(i).compare(o2.types.get(i));
				res.add(names.get(i), t);
			}
			return res;

		} else
			return this;
	}
}
