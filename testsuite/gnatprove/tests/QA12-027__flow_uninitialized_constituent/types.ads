package Types
is
   type T is private;

private
   pragma SPARK_Mode (Off);
   type Null_Tagged_Record is tagged record
      null;
   end record;

   type T is access Null_Tagged_Record;
end;
