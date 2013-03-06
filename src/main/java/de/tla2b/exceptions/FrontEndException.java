package de.tla2b.exceptions;

import tla2sany.modanalyzer.SpecObj;

@SuppressWarnings("serial")
public class FrontEndException extends TLA2BException{

	public SpecObj spec;
	public FrontEndException(String e){
		super(e);
	}

	public FrontEndException(String string, SpecObj spec) {
		super(string);
		this.spec = spec;
	}
}
