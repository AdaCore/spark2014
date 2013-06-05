package body Raw_Data
is

   State : Integer;

   procedure Read (Value : out Integer)
   is
   begin
      Value := State;
   end Read;

end Raw_Data;