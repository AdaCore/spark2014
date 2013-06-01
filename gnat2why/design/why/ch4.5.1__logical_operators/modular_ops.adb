package body Modular_Ops is

   function My_And (Left, Right : byte) return byte is
   begin
      return Left and Right;
   end My_And;

   function My_Or (Left, Right : byte) return byte is
   begin
      return Left or Right;
   end My_Or;

   function My_Xor (Left, Right : byte) return byte is
   begin
      return Left xor Right;
   end My_Xor;

end Modular_Ops;

