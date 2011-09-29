package types;

public class ModelValueType extends MyType implements IType{

	public ModelValueType() {
		super(MODELVALUE);
	}

	public String toString(){
		return "Enum";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}
}
