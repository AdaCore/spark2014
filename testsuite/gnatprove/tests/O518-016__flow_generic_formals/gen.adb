package body Gen is
   procedure P is
   begin
      Y := not Bounded;
   end P;

   function Get_Bounded return Boolean is (Bounded);
begin
   P;
end Gen;
