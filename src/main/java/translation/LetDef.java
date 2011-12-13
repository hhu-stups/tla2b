/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.ArrayList;
import java.util.LinkedHashMap;

import tla2sany.semantic.OpDefNode;

public class LetDef {
	private String name;
	private OpDefNode node;
	private ArrayList<String> parameters;
	private LinkedHashMap<String, LetDef> localDefintions;
	
	public LetDef(String name, OpDefNode node, ArrayList<String> parameters, LinkedHashMap<String, LetDef> lets){
		this.name = name;
		this.node = node;
		this.parameters = parameters;
		this.localDefintions = lets;
	}

	public String getName() {
		return name;
	}

	public OpDefNode getNode() {
		return node;
	}

	public ArrayList<String> getParameters() {
		return parameters;
	}

	/**
	 * @return the dContext
	 */
	public LinkedHashMap<String, LetDef> getlocalDefinition() {
		return localDefintions;
	}


	
	
	
}
