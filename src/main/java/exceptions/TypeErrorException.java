package exceptions;

import translation.MyException;

@SuppressWarnings("serial")
public class TypeErrorException extends MyException {


	public TypeErrorException(String s) {
		super(s);
	}
}
