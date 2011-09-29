package types;


public class IntType extends MyType implements IType {

	public IntType() {
		super(INT);
	}
	
	@Override
	public String toString(){
		return "INTEGER";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

}
