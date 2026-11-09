package Bad_DIC with SPARK_Mode is

   type T is private with Default_Initial_Condition => True;

private

   type T is record
      G : Boolean;
   end record;

end Bad_DIC;
