package body P is
   protected body PT is
      procedure Flip is
      begin
         C3.C2.C1 := not C3.C2.C1;
      end;
   end PT;

   procedure Flip (C3 : in out R2) is
   begin
      C3.C2.C1 := not C3.C2.C1;
   end Flip;
end P;
