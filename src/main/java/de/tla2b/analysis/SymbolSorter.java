/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Hashtable;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;

public class SymbolSorter {
	private ModuleNode moduleNode;

	public SymbolSorter(ModuleNode moduleNode) {
		this.moduleNode = moduleNode;
	}

	public void sort() {
		// sort constants
		Arrays.sort(moduleNode.getConstantDecls(), new OpDeclNodeComparator());
		// sort variables
		Arrays.sort(moduleNode.getVariableDecls(), new OpDeclNodeComparator());
		// sort definitions
		Arrays.sort(moduleNode.getOpDefs(), new OpDefNodeComparator());
	}
	
	public static void sortDeclNodes(OpDeclNode[] opDeclNodes){
		Arrays.sort(opDeclNodes, new OpDeclNodeComparator());
	}
	
	public static void sortOpDefNodes(OpDefNode[] opDefNodes){
		Arrays.sort(opDefNodes, new OpDefNodeComparator());
	}

	public static  Hashtable<String, OpDefNode> getDefsHashTable(OpDefNode[] opDefNodes){
		 Hashtable<String, OpDefNode> definitions = new Hashtable<String, OpDefNode>();
		for (int i = 0; i < opDefNodes.length; i++) {
			OpDefNode def = opDefNodes[i];
			// Definition in this module
//			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
//					.getName().toString())
//					|| StandardModules.contains(def.getSource()
//							.getOriginallyDefinedInModuleNode().getName()
//							.toString())) {
//				continue;
//			}
			definitions.put(def.getName().toString(), def);
		}
		return definitions;
	}
	
}

class OpDeclNodeComparator implements Comparator<OpDeclNode> {
	public int compare(OpDeclNode a, OpDeclNode b) {
		if (a.getUid() < b.getUid())
			return -1;
		if (a.getUid() > b.getUid())
			return 1;
		return 0;
	}
}

class OpDefNodeComparator implements Comparator<OpDefNode> {
	public int compare(OpDefNode a, OpDefNode b) {
		if (a.getLocation().equals(b.getLocation())) {
			if (a.getSource().getUid() < b.getSource().getUid())
				return -1;
			if (a.getSource().getUid() > b.getSource().getUid())
				return 1;
			return 0;
		}
		if (a.getUid() < b.getUid())
			return -1;
		if (a.getUid() > b.getUid())
			return 1;
		return 0;
	}
}