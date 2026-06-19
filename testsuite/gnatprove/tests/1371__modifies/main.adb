procedure Main with SPARK_Mode is

   --  Check that there is no shadowing when several hidden states have the
   --  same whort name.

   package Nested_1 with Abstract_State => S is
      procedure Write with
        Global => (In_Out => S);
   end Nested_1;
   package body Nested_1 with SPARK_Mode => Off is
      X : Integer;
      procedure Write is
      begin
         X := X / 2;
      end Write;
   end Nested_1;

   package Nested_2 with Abstract_State => S is
      procedure Write with
        Global => (In_Out => S);
   end Nested_2;
   package body Nested_2 with SPARK_Mode => Off is
      X : Integer;
      procedure Write is
      begin
         X := X / 2;
      end Write;
   end Nested_2;

   procedure Write (B : Boolean) with
     Modifies =>
       (Nested_1.S when B,
        Nested_2.S when not B);

   procedure Write (B : Boolean) is
   begin
      if B then
         Nested_1.Write;
      else
         Nested_2.Write;
      end if;
   end Write;

begin
   null;
end Main;
