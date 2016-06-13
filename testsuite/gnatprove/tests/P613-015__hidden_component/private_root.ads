package Private_Root with SPARK_Mode is
   type Root is tagged private;

   procedure P;
private
   type Root is tagged record
      Hidden_F : Integer;
   end record;
end Private_Root;
