/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package pprint;

public class DContext {
	public StringBuilder indent;
	
	
	public DContext(){
		indent = new StringBuilder();
	}
	
	public DContext(String indent){
		this.indent = new StringBuilder(indent);
	}
}
