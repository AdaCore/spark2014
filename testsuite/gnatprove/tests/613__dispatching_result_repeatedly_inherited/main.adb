procedure Main with SPARK_Mode is
   package A is
      type Root is tagged null record;
      function Create return Root is (null record);
   end A;
   use A;

   package B is
      type GrandChild is new Root with private;
      Witness : constant GrandChild;
   private
      type Child is new Root with null record;
      type GrandChild is new Child with null record;
      Witness : constant GrandChild := (null record);
   end B;
   use B;

   X : Root'Class := Witness;
begin
   X := A.Create;
end Main;
