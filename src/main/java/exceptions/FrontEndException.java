package exceptions;

import tla2sany.modanalyzer.SpecObj;

@SuppressWarnings("serial")
public class FrontEndException extends Exception {

	public SpecObj spec;
	public FrontEndException(String e){
		super(e);
	}

	public FrontEndException(String string, SpecObj spec) {
		super(string);
		this.spec = spec;
	}
}
