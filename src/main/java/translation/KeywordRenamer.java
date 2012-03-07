/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;

public class KeywordRenamer implements TranslationGlobals{
	private ModuleNode moduleNode;
	private Hashtable<String, SymbolNode> symbolTable = new Hashtable<String, SymbolNode>();
	private final static Set<String> KEYWORDS = new HashSet<String>();
	static {
		KEYWORDS.add("seq");
		KEYWORDS.add("left");
		KEYWORDS.add("right");
		KEYWORDS.add("max");
		KEYWORDS.add("min");
		KEYWORDS.add("succ");
		KEYWORDS.add("pred");
		KEYWORDS.add("dom");
		KEYWORDS.add("ran");
		KEYWORDS.add("fnc");
		KEYWORDS.add("rel");
		KEYWORDS.add("id");
		KEYWORDS.add("card");
		KEYWORDS.add("POW");
		KEYWORDS.add("POW1");
		KEYWORDS.add("FIN");
		KEYWORDS.add("FIN1");
		KEYWORDS.add("size");
		KEYWORDS.add("rev");
		KEYWORDS.add("first");
		KEYWORDS.add("last");
		KEYWORDS.add("front");
		KEYWORDS.add("tail");
		KEYWORDS.add("conc");
		KEYWORDS.add("struct");
		KEYWORDS.add("rec");
		KEYWORDS.add("tree");
		KEYWORDS.add("btree");
		KEYWORDS.add("skip");
		KEYWORDS.add("ANY");
		KEYWORDS.add("WHERE");
		KEYWORDS.add("END");
		KEYWORDS.add("BE");
		KEYWORDS.add("VAR");
		KEYWORDS.add("ASSERT");
		KEYWORDS.add("CHOICE");
		KEYWORDS.add("OR");
		KEYWORDS.add("SELECT");
		KEYWORDS.add("EITHER");
		KEYWORDS.add("WHEN");
		KEYWORDS.add("BEGIN");
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("REFINEMENT");
		KEYWORDS.add("IMPLEMENTATION");
		KEYWORDS.add("SETS");
		KEYWORDS.add("CONSTRAINTS");
		KEYWORDS.add("MODEL");
		KEYWORDS.add("SYSTEM");
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("EVENTS");
		KEYWORDS.add("OPERATIONS");
	}
	
	private Set<String> newNames = new HashSet<String>();
	
	public KeywordRenamer(ModuleNode moduleNode){
		this.moduleNode = moduleNode;
		fillSymbolTable();
	}
	
	public void start(){
		Enumeration<String> usedSymbols = symbolTable.keys();
		while (usedSymbols.hasMoreElements()) {
			String name = (String) usedSymbols.nextElement();
			if(existingName(name)){
				String newName = createName(name);
				newNames.add(newName);
				SymbolNode s = symbolTable.get(name);
				s.setToolObject(NEW_NAME, newName);
			}
		}
		
		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			Boolean isUsed = (Boolean) def
					.getToolObject(PRINT_DEFINITION);
			if (isUsed != null) {
				String defName = def.getName().toString();
				String newName = "";
				if(existingName(defName)){
					newName = createName(defName);
					def.setToolObject(NEW_NAME, newName);
				}
				else if(defName.contains("!")){
					newName = defName.replace('!', '_');
					def.setToolObject(NEW_NAME, newName);
				}else if(defName.startsWith("\\")){
					newName = defName.substring(1);
					def.setToolObject(NEW_NAME, newName);
					if(!def.getSource().equals(def))
						def.getSource().setToolObject(NEW_NAME, newName);
				}
				newNames.add(newName);
			}
		}
		
	}
	
	private void fillSymbolTable(){
		//Variables
		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode v = moduleNode.getVariableDecls()[i];
			symbolTable.put(v.getName().toString(), v);
		}
		//constants
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode v = moduleNode.getConstantDecls()[i];
			symbolTable.put(v.getName().toString(), v);
		}
		
		// definitions
	}
	
	private boolean existingName(String name){
		if(newNames.contains(name) || KEYWORDS.contains(name)){
			return true;
		}else 
			return false;
	}
	
	protected String createName(String name) {
		String res = name;
		for (int i = 1; existingName(res); i++) {
			res = name+"_" + i;
		}
		return res;
	}
}
