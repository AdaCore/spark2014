package body P is

   protected body PP is
      procedure P is
         type T is new Integer range 1 .. C;
         X : T := 3; --@RANGE_CHECK:FAIL
      begin
         null;
      end P;
      function Prot return Boolean is (B and Dummy);
   end;

   X : PP (True, 10);
   C : constant Boolean := X.B;
   pragma Assert (C);
   D : constant Boolean := X.Prot;
   pragma Assume (D);
   E : constant Boolean := X.Prot;
   pragma Assert (E); --@ASSERT:FAIL

begin
   X.P;
end;
