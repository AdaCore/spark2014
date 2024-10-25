package Tagged_DIC with SPARK_Mode is
   type Root_2 is tagged private;
private
   pragma SPARK_Mode (Off);
   type Root_2 is tagged record
      X : Integer;
   end record;
end Tagged_Dic;
