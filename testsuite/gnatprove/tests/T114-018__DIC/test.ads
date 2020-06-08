package Test with
  SPARK_Mode
is

   type Element is private with
     Default_Initial_Condition =>
       False;

   type Sequence is private with
     Default_Initial_Condition =>
       False;

private

   type Element is null record;

   type Sequence is array (Positive) of Element;

end Test;
