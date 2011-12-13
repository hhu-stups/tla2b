/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.LinkedHashMap;


public class DContext {
	private String prefix;
	protected StringBuilder indent;
	protected LinkedHashMap<String, LetDef> localDefinitions;
	
	
	public DContext(){
		this.prefix = "";
		indent = new StringBuilder();
		localDefinitions = new LinkedHashMap<String, LetDef>();
	}
	
	public DContext(String prefix){
		this.prefix = prefix;
		indent = new StringBuilder();
		localDefinitions = new LinkedHashMap<String, LetDef>();
	}
	
	public DContext(String prefix, String indent){
		this.prefix = prefix;
		this.indent = new StringBuilder(indent);
		localDefinitions = new LinkedHashMap<String, LetDef>();
	}

	public String getPrefix() {
		return prefix;
	}

	public void setPrefix(String prefix) {
		this.prefix = prefix;
	}

}
