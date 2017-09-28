with Generic_Child;
package Private_Child with SPARK_Mode is

   type Root (C : Natural) is tagged null record;

   package P_C is new Generic_Child (Root);

   X : P_C.Child (10);
end Private_Child;
