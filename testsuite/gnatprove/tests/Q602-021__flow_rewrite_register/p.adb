package body P with SPARK_Mode is

   procedure nnd (N : integer);
   pragma Export (Ada, nnd);
   procedure New_Node_Debugging_Output (N : integer) renames nnd;

   procedure Dummy with SPARK_Mode => Off is
   begin
      pragma Debug (New_Node_Debugging_Output (0));
   end;

   procedure nnd (N : integer) is
   begin
      pragma Assert (N = 0);
   end;

end;
