package Test with
  SPARK_Mode
is

   type Context_Type (First : Positive := Positive'First; Last : Positive := Positive'Last) is private with
     Default_Initial_Condition => False;

   procedure Initialize (Context : out Context_Type; First : Positive; Last : Positive) with
     Pre => not Context'Constrained and First <= Last;

   function Foo return Boolean;

private

   type Context_Type (First : Positive := Positive'First; Last : Positive := Positive'Last) is
      record
         Index  : Positive := Positive'First;
   end record with
     Dynamic_Predicate => (First <= Last and Index >= First and Index <= Last);

end Test;
