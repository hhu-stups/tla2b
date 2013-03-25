package de.tla2b.global;


import java.util.Hashtable;

import util.UniqueString;

public class BBuiltInOPs implements BBuildIns{
	private static Hashtable<UniqueString, Integer> B_Opcode_Table;
	static {
		B_Opcode_Table = new Hashtable<UniqueString, Integer>();
		B_Opcode_Table.put(OP_dotdot, B_OPCODE_dotdot);
		B_Opcode_Table.put(OP_plus, B_OPCODE_plus);
		B_Opcode_Table.put(OP_minus, B_OPCODE_minus);
		B_Opcode_Table.put(OP_times, B_OPCODE_times);
		B_Opcode_Table.put(OP_div, B_OPCODE_div);
		B_Opcode_Table.put(OP_mod, B_OPCODE_mod);
		B_Opcode_Table.put(OP_exp, B_OPCODE_exp);
		B_Opcode_Table.put(OP_uminus, B_OPCODE_uminus);
		
		B_Opcode_Table.put(OP_lt, B_OPCODE_lt);
		B_Opcode_Table.put(OP_leq, B_OPCODE_leq);
		B_Opcode_Table.put(OP_gt, B_OPCODE_gt);
		B_Opcode_Table.put(OP_geq, B_OPCODE_geq);
		B_Opcode_Table.put(OP_bool, B_OPCODE_bool);
		B_Opcode_Table.put(OP_true, B_OPCODE_true);
		B_Opcode_Table.put(OP_false, B_OPCODE_false);
		B_Opcode_Table.put(OP_nat, B_OPCODE_nat);
		B_Opcode_Table.put(OP_int, B_OPCODE_int);
		B_Opcode_Table.put(OP_string, B_OPCODE_string);
		
		B_Opcode_Table.put(OP_finite, B_OPCODE_finite);
		B_Opcode_Table.put(OP_card, B_OPCODE_card);
		
		B_Opcode_Table.put(OP_len, B_OPCODE_len);
		B_Opcode_Table.put(OP_append, B_OPCODE_append);
		B_Opcode_Table.put(OP_seq, B_OPCODE_seq);
		B_Opcode_Table.put(OP_head, B_OPCODE_head);
		B_Opcode_Table.put(OP_tail, B_OPCODE_tail);
		B_Opcode_Table.put(OP_subseq, B_OPCODE_subseq);
		B_Opcode_Table.put(OP_conc, B_OPCODE_conc);
		
		B_Opcode_Table.put(OP_min, B_OPCODE_min);
		B_Opcode_Table.put(OP_max, B_OPCODE_max);
		B_Opcode_Table.put(OP_setprod, B_OPCODE_setprod);
		B_Opcode_Table.put(OP_setsum, B_OPCODE_setsum);
		B_Opcode_Table.put(OP_permseq, B_OPCODE_permseq);
		
		B_Opcode_Table.put(OP_pow1, B_OPCODE_pow1);
		
		//relations
		B_Opcode_Table.put(OP_rel_inverse, B_OPCODE_rel_inverse);
		
		
	}
	
	public static boolean contains(UniqueString s){
		return B_Opcode_Table.containsKey(s);
	}
	
	public static int getOpcode(UniqueString s){
		return B_Opcode_Table.get(s);
	}
}
