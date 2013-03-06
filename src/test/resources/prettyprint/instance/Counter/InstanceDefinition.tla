-------------- MODULE InstanceDefinition ----------------
VARIABLES c
val == 5 (* the val definition of the Counter module will be automatically overriden by SANY  *)
INSTANCE Counter WITH x <- c, start <- 0
=================================