package de.tla2b.global;

import util.UniqueString;

public interface BBuildIns {
	public static final UniqueString OP_dotdot = UniqueString
			.uniqueStringOf("..");
	public static final UniqueString OP_plus = UniqueString.uniqueStringOf("+");
	public static final UniqueString OP_minus = UniqueString
			.uniqueStringOf("-");
	public static final UniqueString OP_times = UniqueString
			.uniqueStringOf("*");
	public static final UniqueString OP_div = UniqueString
			.uniqueStringOf("\\div");
	public static final UniqueString OP_mod = UniqueString.uniqueStringOf("%");
	public static final UniqueString OP_exp = UniqueString.uniqueStringOf("^");

	public static final UniqueString OP_uminus = UniqueString
			.uniqueStringOf("-.");

	public static final UniqueString OP_lt = UniqueString.uniqueStringOf("<");
	public static final UniqueString OP_leq = UniqueString
			.uniqueStringOf("\\leq");
	public static final UniqueString OP_gt = UniqueString.uniqueStringOf(">");
	public static final UniqueString OP_geq = UniqueString
			.uniqueStringOf("\\geq");

	public static final UniqueString OP_nat = UniqueString
			.uniqueStringOf("Nat");
	public static final UniqueString OP_int = UniqueString
			.uniqueStringOf("Int");
	public static final UniqueString OP_bool = UniqueString
			.uniqueStringOf("BOOLEAN");
	public static final UniqueString OP_true = UniqueString
			.uniqueStringOf("TRUE");
	public static final UniqueString OP_false = UniqueString
			.uniqueStringOf("FALSE");
	public static final UniqueString OP_string = UniqueString
			.uniqueStringOf("STRING");

	// Sets
	public static final UniqueString OP_card = UniqueString
			.uniqueStringOf("Cardinality");
	public static final UniqueString OP_finite = UniqueString
			.uniqueStringOf("IsFiniteSet");

	// Sequences
	public static final UniqueString OP_len = UniqueString
			.uniqueStringOf("Len");
	public static final UniqueString OP_append = UniqueString
			.uniqueStringOf("Append");
	public static final UniqueString OP_seq = UniqueString
			.uniqueStringOf("Seq");
	public static final UniqueString OP_head = UniqueString
			.uniqueStringOf("Head");
	public static final UniqueString OP_tail = UniqueString
			.uniqueStringOf("Tail");
	public static final UniqueString OP_subseq = UniqueString
			.uniqueStringOf("SubSeq");
	public static final UniqueString OP_conc = UniqueString
	.uniqueStringOf("\\o");
	
	//TLA2B
	public static final UniqueString OP_min = UniqueString
			.uniqueStringOf("MinOfSet");
	public static final UniqueString OP_max = UniqueString
			.uniqueStringOf("MaxOfSet");
	public static final UniqueString OP_setprod = UniqueString
			.uniqueStringOf("SetProduct");
	public static final UniqueString OP_setsum = UniqueString
			.uniqueStringOf("SetSummation");
	public static final UniqueString OP_permseq = UniqueString
			.uniqueStringOf("PermutedSequences");

	//BBuildIns
	public static final UniqueString OP_pow1 = UniqueString
			.uniqueStringOf("POW1");
	
	
	//Relations
	public static final UniqueString OP_rel_inverse = UniqueString
			.uniqueStringOf("rel_inverse");
	
	public static final int B_OPCODE_dotdot = 1;
	public static final int B_OPCODE_plus = 2;
	public static final int B_OPCODE_minus = 3;
	public static final int B_OPCODE_times = 4;
	public static final int B_OPCODE_div = 5;
	public static final int B_OPCODE_exp = 6;
	public static final int B_OPCODE_uminus = 7;
	public static final int B_OPCODE_mod = 8;

	public static final int B_OPCODE_lt = B_OPCODE_mod + 1;
	public static final int B_OPCODE_leq = B_OPCODE_mod + 2;
	public static final int B_OPCODE_gt = B_OPCODE_mod + 3;
	public static final int B_OPCODE_geq = B_OPCODE_mod + 4;

	public static final int B_OPCODE_nat = B_OPCODE_geq + 1;
	public static final int B_OPCODE_bool = B_OPCODE_geq + 2;
	public static final int B_OPCODE_true = B_OPCODE_geq + 3;
	public static final int B_OPCODE_false = B_OPCODE_geq + 4;
	public static final int B_OPCODE_int = B_OPCODE_geq + 5;
	public static final int B_OPCODE_string = B_OPCODE_geq + 6;

	public static final int B_OPCODE_finite = B_OPCODE_string + 1;
	public static final int B_OPCODE_card = B_OPCODE_string + 2;

	public static final int B_OPCODE_len = B_OPCODE_card + 1;
	public static final int B_OPCODE_append = B_OPCODE_card + 2;
	public static final int B_OPCODE_seq = B_OPCODE_card + 3;
	public static final int B_OPCODE_head = B_OPCODE_card + 4;
	public static final int B_OPCODE_tail = B_OPCODE_card + 5;
	public static final int B_OPCODE_subseq = B_OPCODE_card + 6;
	public static final int B_OPCODE_conc = B_OPCODE_card + 7;

	public static final int B_OPCODE_min = B_OPCODE_conc + 1;
	public static final int B_OPCODE_max = B_OPCODE_conc + 2;
	public static final int B_OPCODE_setprod = B_OPCODE_conc + 3;
	public static final int B_OPCODE_setsum = B_OPCODE_conc + 4;
	public static final int B_OPCODE_permseq = B_OPCODE_conc + 5;
	
	public static final int B_OPCODE_pow1 = B_OPCODE_permseq + 1;
	
	
	public static final int B_OPCODE_rel_inverse = B_OPCODE_pow1 + 1;
}
