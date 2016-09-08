procedure Division_By_Zero is

   type Oper is (D, M, R);
   type Unsigned is mod 2**32;
   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;

   procedure Oper_Integer (Op : Oper; X, Y : Integer; U : out Integer) is
   begin
      case Op is
         when D => U := X / Y;
         when M => U := X mod Y;
         when R => U := X rem Y;
      end case;
   end Oper_Integer;

   procedure Oper_Unsigned (Op : Oper; X, Y : Unsigned; U : out Unsigned) is
   begin
      case Op is
         when D => U := X / Y;
         when M => U := X mod Y;
         when R => U := X rem Y;
      end case;
   end Oper_Unsigned;

   procedure Div_Float (X, Y : Float; U : out Float) is
   begin
      U := X / Y;
   end Div_Float;

   procedure Div_Fixed (X, Y : Float; U : out Float) is
   begin
      U := X / Y;
   end Div_Fixed;

   procedure Exp_Float (X : Float; Y : Integer; U : out Float) is
   begin
      U := X ** Y;
   end Exp_Float;
begin
   null;
end Division_By_Zero;
