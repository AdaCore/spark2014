procedure Null_Record
is
   type Nothing is null record;
   type R is record
      null;
   end record;
begin
   null;
end Null_Record;
