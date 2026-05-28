--  Test declarations in mode Auto. No violations should be emitted.

package Auto is

   package Test_Type_No_SPARK is
      package Nested with SPARK_Mode => Off is
         type Int_Acc is access Integer;
         type Data_Array is array (Positive range <>) of not null Int_Acc;
      end Nested;
      use Nested;

      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer is
        (C.Content (I))
          with Pre => Has_Element (C, I);

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element");
   end Test_Type_No_SPARK;

   package Test_Prim_No_SPARK is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;

      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer is
        (C.Content (I))
          with Pre => Has_Element (C, I);

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with SPARK_Mode => Off,
          Annotate => (GNATprove, Iterable_For_Proof, "Element");
   end Test_Prim_No_SPARK;

end Auto;
