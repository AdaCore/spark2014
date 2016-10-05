generic
  type T (<>) is tagged private;
package Generic_Child with SPARK_Mode is
   package Nested is
      type C is new T with private with Default_Initial_Condition =>
        Is_Valid (C);

      function Is_Valid (X : C) return Boolean;
   private
      pragma SPARK_Mode (Off);
      type C is new T with null record;

      function Is_Valid (X : C) return Boolean is (True);
   end Nested;

   type Child is new Nested.C with null record;
end Generic_Child;
