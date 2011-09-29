package exceptions;

import translation.MyException;

@SuppressWarnings("serial")
public class ModuleErrorException extends MyException{
	public ModuleErrorException(String e){
		super(e);
	}

}
