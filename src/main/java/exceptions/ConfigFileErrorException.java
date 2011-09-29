package exceptions;

import translation.MyException;

@SuppressWarnings("serial")
public class ConfigFileErrorException extends MyException{

	public ConfigFileErrorException(String s) {
		super(s);
	}
}
