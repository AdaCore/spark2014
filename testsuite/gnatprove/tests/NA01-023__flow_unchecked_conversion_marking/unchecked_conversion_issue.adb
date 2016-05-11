with Unchecked_Conversion;

procedure Unchecked_Conversion_Issue
  with SPARK_Mode
is

   type Record_T is
      record
         Word_1 : Short_Integer;
         Word_2 : Short_Integer;
      end record;

   function UCC is new Unchecked_Conversion (Integer,
                                             Record_T);
   Result : Record_T;
begin
   Result := UCC (0);
end Unchecked_Conversion_Issue;
