package Bad_Array with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;
   subtype Pos_Array is Int_Array with Dynamic_Predicate =>
     (for all I of Pos_Array => I in Positive);
   function Foo return Pos_Array;
end;
