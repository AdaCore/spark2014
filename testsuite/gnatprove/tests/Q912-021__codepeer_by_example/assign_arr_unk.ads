package Assign_Arr_Unk is
   type Arr is array (Integer range <>) of Integer;
   procedure Assign (X : out Arr; Y : in Integer);
end Assign_Arr_Unk;
