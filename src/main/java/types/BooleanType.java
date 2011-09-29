package types;


public class BooleanType extends MyType implements IType{

	private boolean isBoolValue;
	
	public BooleanType() {
		super(BOOLEAN);
		isBoolValue = false;
	}
	public boolean isBoolValue() {
		return isBoolValue;
	}
	public void setBoolValue(boolean isBoolValue) {
		this.isBoolValue = isBoolValue;
	}
	public BooleanType(boolean isBV) {
		super(BOOLEAN);
		isBoolValue = isBV;
	}
	
	@Override
	public String toString(){
		return "BOOL";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

}
