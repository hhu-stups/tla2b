/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package exceptions;

@SuppressWarnings("serial")
public class SemanticErrorException extends MyException {
	
	public SemanticErrorException(String e){
		super(e);
	}

}
