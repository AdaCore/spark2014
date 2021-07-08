procedure Main with SPARK_Mode is
     type Root is tagged record
        F : Integer;
     end record;

     type Child is new Root with record
        G : Integer;
     end record;

     type Grand_Child is new Child with record
        H : Integer;
     end record;

   X : Grand_Child := (1, 2, 3);
   Y : Root'Class := Root'Class (X);
   Z : Child'Class := Child'Class (X);
   W : Child'Class := Child'Class (Grand_Child'(1, 2, 4));
begin
   pragma Assert (Grand_Child (Y) = Grand_Child (Z));
   pragma Assert (Child (Z) = Child (W));
   pragma Assert (Grand_Child (Z) /= Grand_Child (W));
   pragma Assert (Z /= W);
end Main;
