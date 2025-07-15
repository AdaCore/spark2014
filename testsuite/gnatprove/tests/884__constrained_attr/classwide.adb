procedure Classwide is
   type T is tagged record
      C : Integer;
   end record;

   X : T'Class := T'(C => 1);
begin
   pragma Assert (not X'Constrained); --@ASSERT:PASS
end;
