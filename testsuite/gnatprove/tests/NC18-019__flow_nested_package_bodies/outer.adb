package body Outer is
   procedure P (X : out Integer) is
      package Nested
        with Abstract_State => State,
             Initializes    => (State, Used)
      is
         Used : Integer := 0;

         function F return Integer;
      end Nested;

      package body Nested
        with Refined_State => (State => (Nested_Var, Nested_Var2))
      is
         Nested_Var  : Integer := 5;
         Nested_Var2 : Integer := 10;

         function F return Integer is (Nested_Var + Nested_Var2 + Used);
      end Nested;

   begin
      X := Nested.F;
   end P;

   procedure P2 (X : out Integer) is
      package Nested
        with Initializes => Used
      is
         Used   : Integer := 0;  --  OK
         Unused : Integer := 0;  --  ineffective initialization

         function F return Integer;
      end Nested;

      package body Nested is
         Nested_Var  : Integer := 5;
         Nested_Var2 : Integer;

         function F return Integer is (Nested_Var + Nested_Var2 + Used);
      begin
         Nested_Var2 := 10;
      end Nested;

   begin
      X := Nested.F;
   end P2;

   procedure P3 is
      generic
      package G is
         Unused : Integer;
      end G;

      package body G is
      begin
         Unused := 123;
         pragma Assert (Unused /= 456);
      end G;

      package Inst is new G;
   begin
      null;
   end P3;

   procedure P4 (X : out Integer) is
      package Nested
        with Initializes => Used
      is
         Used : Integer;

         function F return Integer;
      end Nested;

      package body Nested is
         Nested_Var  : Integer := 5;
         Nested_Var2 : Integer := 10;

         function F return Integer is (Nested_Var + Nested_Var2 + Used);
      begin
         Used := 0;
      end Nested;

   begin
      X := Nested.F;
   end P4;
end Outer;
