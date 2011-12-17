/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import tla2sany.semantic.ExprNode;

public class BInit {
	private String prefix;
	private ExprNode node;
	public BInit(String prefix, ExprNode node){
		this.prefix = prefix;
		this.node = node;
	}
	public ExprNode getNode() {
		return node;
	}
	public String getPrefix() {
		return prefix;
	}
}
