package Test_2 with SPARK_Mode is

   type Context_Type (First : Positive := Positive'First; Last : Positive := Positive'Last) is private with
     Default_Initial_Condition => First < Last;

private

   type Context_Type (First : Positive := Positive'First; Last : Positive := Positive'Last) is
      record
         Index  : Positive := First;
   end record with
     Dynamic_Predicate => (First <= Last and Index >= First and Index <= Last);

end Test_2;
