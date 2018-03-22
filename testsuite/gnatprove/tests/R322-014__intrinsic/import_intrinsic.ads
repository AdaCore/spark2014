package Import_Intrinsic with SPARK_Mode is
   type New_Float is private;
   function "<" (Left, Right : New_Float) return Boolean with SPARK_Mode => Off;
private
   pragma SPARK_Mode (Off);
   type New_Float is new Float;
   pragma Import (Intrinsic, "<");
end Import_Intrinsic;
