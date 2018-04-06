package body A is

   State : Integer := Integer'Last;

   function Get return Integer is (State);

   procedure Mutate is
   begin
      State := State + 1;
   end Mutate;
end A;
