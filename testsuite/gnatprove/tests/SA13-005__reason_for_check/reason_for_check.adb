procedure Reason_For_Check is

   --  range checks on parameters

   X1, X2 : Integer := 0;
   Y1, Y2 : Positive := 1;

   procedure Oper_Natural (V : Natural; W : out Natural; Z : in out Natural) with
     Pre => V < 1000 and Z < 1000
   is
   begin
      Z := Z + 1;
      W := V;
   end Oper_Natural;

   procedure Oper_Int_Pos with Pre => True is
   begin
      Oper_Natural (X1, X1, X2);
      Oper_Natural (Y1, Y1, Y2);
   end Oper_Int_Pos;

   --  index checks

   function Get (S : String; J : Positive) return Character is
   begin
      return S(J);  --<<-- medium: array index check might fail
   end Get;

   procedure Set (S : in out String; J : Positive; C : Character) is
   begin
      S(J) := C;  --<<-- medium: array index check might fail
   end Set;

   --  overflow checks

   type Oper is (Minus, AbsVal, Add, Sub, Mult, Div, Exp);
   type Unsigned is mod 2**32;
   Small : constant := 1.0 / 2.0**7;
   type Fixed is delta Small range -1.0 .. 1.0 - Small
     with Size => 8;

   procedure Oper_Integer (Op : Oper; X, Y : Integer; E : Natural; U : out Integer) is
   begin
      case Op is
         when Minus  => U := -X;  --<<-- medium: overflow check might fail
         when AbsVal => U := abs X;  --<<-- medium: overflow check might fail
         when Add    => U := X + Y;  --<<-- medium: overflow check might fail
         when Sub    => U := X - Y;  --<<-- medium: overflow check might fail
         when Mult   => U := X * Y;  --<<-- medium: overflow check might fail
         when Div    => U := X / Y;  --<<-- medium: overflow check might fail
         when Exp    => U := X ** E;  --<<-- medium: overflow check might fail
      end case;
   end Oper_Integer;

   procedure Oper_Float (Op : Oper; X, Y : Float; E : Natural; U : out Float) is
   begin
      case Op is
         when Minus  => U := -X;
         when AbsVal => U := abs X;
         when Add    => U := X + Y;  --<<-- medium: overflow check might fail
         when Sub    => U := X - Y;  --<<-- medium: overflow check might fail
         when Mult   => U := X * Y;  --<<-- medium: overflow check might fail
         when Div    => U := X / Y;  --<<-- medium: overflow check might fail
         when Exp    => U := X ** E;  --<<-- medium: overflow check might fail
      end case;
   end Oper_Float;

   procedure Oper_Fixed (Op : Oper; X, Y : Fixed; E : Natural; U : out Fixed) is
   begin
      case Op is
         when Minus  => U := -X;  --<<-- medium: overflow check might fail
         when AbsVal => U := abs X;  --<<-- medium: overflow check might fail
         when Add    => U := X + Y;  --<<-- medium: overflow check might fail
         when Sub    => U := X - Y;  --<<-- medium: overflow check might fail
         when Mult   => U := X * Y;  --<<-- medium: overflow check might fail
         when Div    => U := X / Y;  --<<-- medium: overflow check might fail
         when Exp    => null;
      end case;
   end Oper_Fixed;

   --  range checks

   type Enum is (A, B, C, D, E);
   subtype BCD is Enum range B .. D;

   subtype Small_Unsigned is Unsigned range 0 .. 10;

   subtype Natural_Fixed is Fixed range 0.0 .. Fixed'Last;

   subtype Natural_Float is Float range 0.0 .. Float'Last;

   procedure Convert_Enum (X : Enum; U : out BCD) is
   begin
      U := X;  --<<-- medium: range check might fail
   end Convert_Enum;

   procedure Convert_Integer (X : Integer; U : out Natural) is
   begin
      U := X;  --<<-- medium: range check might fail
   end Convert_Integer;

   procedure Convert_Unsigned (X : Unsigned; U : out Small_Unsigned) is
   begin
      U := X;  --<<-- medium: range check might fail
   end Convert_Unsigned;

   procedure Convert_Float (X : Float; U : out Natural_Float) is
   begin
      U := X;  --<<-- medium: range check might fail
   end Convert_Float;

   procedure Convert_Fixed (X : Fixed; U : out Natural_Fixed) is
   begin
      U := X;  --<<-- medium: range check might fail
   end Convert_Fixed;

   --  length checks

   procedure Assign (S : String; T : out String) is
   begin
      T := S;  --<<-- medium: length check might fail
   end Assign;

   type Small_String is new String (1 .. 5);

   function Get_Small (S : String) return Small_String is
   begin
      return Small_String(S);  --<<-- medium: length check might fail
   end Get_Small;

   type Oper_Log is (Logical_And, Logical_Or, Logical_Xor);
   type Mask is array (Natural range <>) of Boolean;

   procedure Oper_Mask (Op : Oper_Log; X : in out Mask; Y : Mask) is
   begin
      case Op is
         when Logical_And => X := X and Y;  --<<-- medium: length check might fail
         when Logical_Or  => X := X or Y;   --<<-- medium: length check might fail
         when Logical_Xor => X := X xor Y;  --<<-- medium: length check might fail
      end case;
   end Oper_Mask;

begin
   Oper_Int_Pos;
end Reason_For_Check;
