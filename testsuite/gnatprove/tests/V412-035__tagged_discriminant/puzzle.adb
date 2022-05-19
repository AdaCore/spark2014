package body Puzzle with SPARK_Mode is
   procedure Try_Set_Word (This : in out Instance) is
   begin
      This.Sol.Add_Word;
   end Try_Set_Word;
end Puzzle;
