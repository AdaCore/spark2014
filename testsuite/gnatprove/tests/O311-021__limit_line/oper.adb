pragma SPARK_Mode;
package body Oper is
   procedure Float_Sub (X, Y : Float; Z : out Long_Float) is separate;
   procedure Float_Sub_2 (X, Y : Float; Z : out Long_Float) is separate;
end Oper;
