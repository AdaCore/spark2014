pragma Extensions_Allowed (On);

procedure Test_Compiler_Generated_Constant with SPARK_Mode is

   function F (X : in out Integer) return Integer
     with Side_Effects,
          Pre => X < Integer'Last,
          Post => X = X'Old + 1
            and then F'Result = X'Old
   is
   begin
      X := X + 1;
      return X - 1;
   end F;

   X : Integer := 0;

   --  Test whether the outputs are correct on "internal" objects.
   --  Full views of deferred constants are considered as "internal" by the
   --  frontend.

   package P is
      C : constant Integer;
   private
      C : constant Integer := F (X); --  illegal, constant in declarative part
   end P;

   type Int_Arr is array (Positive range <>) of Integer;

   A : Int_Arr (1 .. 100) := (others => 0);

begin
   for I in 1 .. F (X) loop --  illegal, function call not in object declaration
      A (I) := 1;
   end loop;
end Test_Compiler_Generated_Constant;
