package Containers with SPARK_Mode is
   type Container (C: Natural) is private with
     Default_Initial_Condition => Length (Container) = 0;

   function Length (X : Container) return Natural;

private

   type Nat_Array is array (Positive range <>) of Natural;

   type Container (C: Natural) is record
      L : Natural := 0;
      V : Nat_Array (1 .. C);
   end record;

   function Length (X : Container) return Natural is (X.L);

end Containers;
