procedure Minimal with SPARK_Mode is
   type Int_Acc is access Integer;
   type Data_Array is array (Positive range <>) of not null Int_Acc;
   type Model_Type (Max : Natural) is record
      Content : Data_Array (1 .. Max);
   end record with
     Iterable =>
       (First => First,
        Next => Next,
        Has_Element => Has_Element,
        Constant_Reference => Constant_Reference);

   function First (C : Model_Type) return Natural is (1);
   function Next (C : Model_Type; I : Natural) return Natural is
     (if I in 1 .. C.Max - 1 then I + 1 else 0);
   function Has_Element (C : Model_Type; I : Natural) return Boolean is
     (I in 1 .. C.Max);
   function Constant_Reference (C : Model_Type; I : Natural) return not null access constant Integer is
     (C.Content (I))
       with Pre => Has_Element (C, I);

   type Container (Max : Natural) is record
      Content : Data_Array (1 .. Max);
   end record with
     Iterable =>
       (First => First,
        Next => Next,
        Has_Element => Has_Element,
        Element => Element);

   function First (C : Container) return Natural is (1);
   function Next (C : Container; I : Natural) return Natural is
     (if I in 1 .. C.Max - 1 then I + 1 else 0);
   function Has_Element (C : Container; I : Natural) return Boolean is
     (I in 1 .. C.Max);
   function Element (C : Container; I : Natural) return Integer is
     (C.Content (I).All)
       with Pre => Has_Element (C, I);

   function Model (C : Container) return Model_Type
     with Global => null,
     Import,
     Annotate => (GNATprove, Iterable_For_Proof, "Model");

begin
   null;
end Minimal;
