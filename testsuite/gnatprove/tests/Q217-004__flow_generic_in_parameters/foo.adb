package body Foo is

   generic
      V : in Integer;
   package G with Initializes => State is
      State : Integer;
      procedure Init (X : out Integer) with Global => null;
   end G;

   package body G is
      procedure Init (X : out Integer) is
      begin
         X := V;
      end Init;
   begin
      State := V;
   end G;

   O_Var     : Integer := 666;
   O_Const   : constant Integer := 42;
   O_Const_V : constant Integer := O_Var;

   package Inst_1 is new G (V => O_Var);     --  Illegal
   package Inst_2 is new G (V => O_Const);   --  Legal
   package Inst_3 is new G (V => O_Const_V); --  Legal

end Foo;
