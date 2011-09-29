package types;

public class Untyped extends MyType{

	public Untyped() {
		super(0);
	}
	public String toString(){
		return "UNTYPED";
	}
	@Override
	public boolean isUntyped() {
		return true;
	}

}
