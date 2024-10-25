with Tagged_DIC; use Tagged_DIC;

package Extensions with SPARK_Mode is
   type Illegal is new Root_2 with private
     with Default_Initial_Condition;
private
   type Illegal is new Root_2 with record
      Y, Z : Integer := 0;
   end record;
end Extensions;
