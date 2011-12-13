procedure A is
begin

   Local_Constant:
   declare
      TC_Max_Loop_Count        : constant Integer := 1000;
      function Test return Boolean is
      begin
         return (TC_Max_Loop_Count = 10);
      end Test;
   begin
      null;
   end Local_Constant;

   Named_Constant:
   declare
      TC_Max_Loop_Count        : constant := 1000;
      function Test return Boolean is
      begin
         return (TC_Max_Loop_Count = 10);
      end Test;
   begin
      null;
   end Named_Constant;

   for I in 1..10 loop
      Loop_Param:
      declare
         function Test return Boolean is
         begin
            return (I = 10);
         end Test;
      begin
         null;
      end Loop_Param;
   end loop;

   In_Param:
   declare
      procedure Outer (X : in Integer) is
         function Test return Boolean is
         begin
            return (X = 10);
         end Test;
      begin
         null;
      end Outer;
   begin
      null;
   end In_Param;

end A;
