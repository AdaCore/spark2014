procedure Overflow_Check is

   type Oper is (Minus, AbsVal, Add, Sub, Mult, Div, Exp);
   type Unsigned is mod 2**32;
   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;

   procedure Oper_Integer (Op : Oper; X, Y : Integer; E : Natural; U : out Integer) is
   begin
      case Op is
         when Minus  => U := -X;
         when AbsVal => U := abs X;
         when Add    => U := X + Y;
         when Sub    => U := X - Y;
         when Mult   => U := X * Y;
         when Div    => U := X / Y;
         when Exp    => U := X ** E;
      end case;
   end Oper_Integer;

   procedure Oper_Float (Op : Oper; X, Y : Float; E : Natural; U : out Float) is
   begin
      case Op is
         when Minus  => U := -X;
         when AbsVal => U := abs X;
         when Add    => U := X + Y;
         when Sub    => U := X - Y;
         when Mult   => U := X * Y;
         when Div    => U := X / Y;
         when Exp    => U := X ** E;
      end case;
   end Oper_Float;

   procedure Oper_Fixed (Op : Oper; X, Y : Fixed; E : Natural; U : out Fixed) is
   begin
      case Op is
         when Minus  => U := -X;
         when AbsVal => U := abs X;
         when Add    => U := X + Y;
         when Sub    => U := X - Y;
         when Mult   => U := X * Y;
         when Div    => U := X / Y;
         when Exp    => null;
      end case;
   end Oper_Fixed;
begin
   null;
end Overflow_Check;
