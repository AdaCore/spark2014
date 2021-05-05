procedure Test_Tagged_Records with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
   end record;
   type Child2 is new Root with record
      G : Integer;
   end record;

   subtype TT is Root'Class with
     Predicate => TT in Child'Class;

   X : TT := Root'Class (Child2'(1, 2)); --  There should be a predicate check here!
begin
   null;
end Test_Tagged_Records;
