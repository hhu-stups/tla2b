package translation;
import java.util.ArrayList;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpApplNode;

// TLA+-action 
// represents a B-operation
public class Action {
	public String name;
	public ExprOrOpArgNode node;
	public ArrayList<String> params= new ArrayList<String>();
	public OpApplNode parent;
	public DefContext defCon;
	
	public Action(String name, ExprOrOpArgNode node){
		this.name = name;
		this.node = node;
		
	}
	public void boundedExists(OpApplNode n){
		if (n==null){
			return;
		}
		params = new ArrayList<String>();
		FormalParamNode[][] ps = n.getBdedQuantSymbolLists();
		for (int i = 0; i < ps.length; i++) {
			for (int j = 0; j < ps[i].length; j++) {
				this.params.add(ps[i][j].getName().toString());
			}
		}
		parent = n;
	}
	
	@Override
	public String toString(){
		String res = name+ " ";
		res += params.toString();
		return res;
	}
}
