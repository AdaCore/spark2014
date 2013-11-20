package body Example is

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) is
   begin
      V := 0;

      if J in A'Range then
         V := A(J);
         A(J) := 0;
      end if;
   end Extract;

end Example;
