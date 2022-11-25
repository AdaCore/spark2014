package Test_DIC with SPARK_Mode is

   package Containers with SPARK_Mode is
      type Container (C: Natural) is private with
        Default_Initial_Condition => Length (Container) /= 1;

      function Length (X : Container) return Natural;

   private

      type Nat_Array is array (Positive range <>) of Natural;

      type Container (C: Natural) is record
         L : Natural := 0;
         V : Nat_Array (1 .. C);
      end record;

      function Length (X : Container) return Natural is (X.L);

   end Containers;

   type Container2 is private with
     Default_Initial_Condition => Length (Container2) /= 2;

   function Length (X : Container2) return Natural;
private
   type Container2 is new Containers.Container (9);

   function Length (X : Container2) return Natural is
     (Containers.Length (Containers.Container (X)));
end Test_DIC;
