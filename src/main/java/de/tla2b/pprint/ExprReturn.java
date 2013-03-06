package de.tla2b.pprint;

public class ExprReturn {
	public StringBuilder out= new StringBuilder();
	private int priority;
	
	
	public ExprReturn(){
		priority = 300;
	}

	public ExprReturn(String s){
		out.append(s);
		priority = 300;
	}
	
	public ExprReturn(StringBuilder out2) {
		out.append(out2);
		priority = 300;
	}
	
	public ExprReturn(StringBuilder out2, int priority2) {
		out.append(out2);
		priority = priority2;
	}

	public ExprReturn(String out2, int priority2) {
		out.append(out2);
		priority = priority2;
	}
	

	
	public StringBuilder getOut() {
		return out;
	}
	public void setOut(StringBuilder out) {
		this.out = out;
	}
	public int getPriority() {
		return priority;
	}
	public void setPriority(int priority) {
		this.priority = priority;
	}
	
	@Override
	public String toString(){
		String s = "P: "+ priority + " Out: " +out.toString();
		return s;
	}

}
