package exceptions;

@SuppressWarnings("serial")
public abstract class MyException extends Exception{

	public MyException(String e){
		super(e);
	}
}
