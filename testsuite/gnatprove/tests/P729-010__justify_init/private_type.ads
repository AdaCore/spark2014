package Private_Type with SPARK_Mode is
   type Fully_Init is private;

   procedure Update (X : in out Fully_Init);
private
   pragma SPARK_Mode (Off);
   type Fully_Init is null record;
end Private_Type;
