package types;

public class StringType extends MyType implements IType {

	public StringType() {
		super(STRING);
	}
	
	@Override
	public String toString(){
		return "STRING";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}
}
