procedure Test_Globals (C : Natural) with SPARK_Mode is
   type My_Array is array (Natural range <>) of Natural;
   subtype My_Array_Stat is My_Array (1 .. 100);
   subtype My_Array_Dyn is My_Array (1 .. C);
   type My_Rec (D : Natural) is record
      F : Natural;
   end record;
   subtype My_Rec_Stat is My_Rec (100);
   subtype My_Rec_Dyn is My_Rec (C);

   AU : My_Array := (1 .. C => 0);
   AS : My_Array_Stat := (1 .. 100 => 0);
   AD : My_Array_Dyn := (1 .. C => 0);
   RU : My_Rec := (D => C, F => 0);
   RS : My_Rec_Stat := (D => 100, F => 0);
   RD : My_Rec_Dyn := (D => C, F => 0);

   function Nested_With_Globals return Boolean is
     (if C > 0 then AU (1) = 0 and then AS (1) = 0 and then AD (1) = 0
      else RU.F = 0 and then RS.F = 0 and then RD.F = 0)
   with Pre => AU'First = 1 and AU'Last = C;

begin
   pragma Assert (Nested_With_Globals);
end Test_Globals;
