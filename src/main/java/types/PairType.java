package types;

import java.util.ArrayList;

public class PairType extends MyType implements IType {

	private MyType first;
	private MyType second;

	public PairType() {
		super(PAIR);
		first = new Untyped();
		second = new Untyped();
	}

	public PairType(MyType f, MyType s) {
		super(PAIR);
		first = f;
		second = s;
	}

	public MyType getFirst() {
		return first;
	}

	public void setFirst(MyType f) {
		this.first = f;
	}

	public MyType getSecond() {
		return second;
	}

	public void setSecond(MyType second) {
		this.second = second;
	}

	@Override
	public String toString() {
		return "(" + first + "*" + second + ")";
	}

	public ArrayList<MyType> getList() {
		ArrayList<MyType> m = new ArrayList<MyType>();
		getL(this, m);
		return m;
	}

	private static void getL(MyType m, ArrayList<MyType> l) {
		if (m.getType() == PAIR) {
			PairType p = (PairType) m;
			l.add(0, p.second);
			getL(p.first, l);
		} else {
			l.add(0, m);
		}
	}

	@Override
	public boolean isUntyped() {
		return first.isUntyped() || second.isUntyped();
	}

	@Override
	public boolean equals(Object o) {
		if (!super.equals(o)) {
			return false;
		}
		MyType t2 = (MyType) o;
		if (this.getType() == UNTYPED || t2.getType() == UNTYPED)
			return true;
		PairType p;
		try {
			p = (PairType) o;
		} catch (Exception e) {
			return false;
		}
		if (this.first.equals(p.getFirst())
				&& this.second.equals(p.getSecond()))
			return true;
		else
			return false;
	}
	
	
	public MyType compare(MyType o) {
		if (!this.equals(o))
			return null;
		
		if(this.getType() == UNTYPED)
			return o;
		if(o.getType() == UNTYPED)
			return this;
		
		
		if (this.isUntyped() || o.isUntyped()) {
			MyType f = first.compare(((PairType) o).getFirst());
			MyType s = second.compare(((PairType) o).getSecond());
			return new PairType(f, s);

		} else
			return this;

	}
	
}
