package body Assign_Arr_Unk is
   procedure Assign (X : out Arr; Y : in Integer) is
   begin
      X (1) := Y + 1;
      X (4) := Y - 1;
   end Assign;
end Assign_Arr_Unk;
