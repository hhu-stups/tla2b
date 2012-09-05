MACHINE DefCapture
PROPERTIES
 Double(2)
 & NotDouble(3)
 & {x|x : {2, 3} & NotDouble(x)} = {3}
DEFINITIONS
 Double(y) == #x_1.(x_1 : 1 .. 10 & x_1 + x_1 = y);

 NotDouble(y) == not(Double(y))
END
