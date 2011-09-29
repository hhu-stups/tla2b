package translation;

import tla2sany.semantic.OpDefNode;

public class Subdefinition {

	private DefContext defCon;
	private OpDefNode node;
	
	public Subdefinition(DefContext defCon, OpDefNode n){
		this.defCon = defCon;
		this.node = n;
	}
	
	public DefContext getDefCon() {
		return defCon;
	}
	public void setDefCon(DefContext con) {
		this.defCon = con;
	}
	public OpDefNode getNode() {
		return node;
	}
	public void setNode(OpDefNode n) {
		this.node = n;
	}
}
