package types;

public class Variable {

	private String name;
	private MyType type;

	public Variable(String n) {
		name = n;
		type = new Untyped();
	}
	
	public Variable(String n, MyType t) {
		name = n;
		type = t;
	}
	

	@Override
	public String toString() {
		return "[Name: " + name + ", Type: " +type+"]";
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}


	public void setType(MyType type) {
		this.type = type;
	}
	
	public MyType getType(){
		return type;
	}
}
