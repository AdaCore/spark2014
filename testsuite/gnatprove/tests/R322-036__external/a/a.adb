package body A is

   State : Integer := Integer'Last;

   function Get return Integer is (State);

   procedure Mutate is
   begin
      State := State / 2;
   end Mutate;
end A;
