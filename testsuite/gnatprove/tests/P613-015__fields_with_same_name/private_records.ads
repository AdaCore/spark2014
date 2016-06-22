package Private_Records with SPARK_Mode is
   type Root is tagged private;

   procedure P;
private
   type Root is tagged record
      F : Integer := 0;
   end record;
end Private_Records;
