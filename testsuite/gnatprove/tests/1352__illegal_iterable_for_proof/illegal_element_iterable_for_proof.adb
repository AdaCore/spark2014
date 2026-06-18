procedure Illegal_Element_Iterable_For_Proof with SPARK_Mode is

   package Test_OK is
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
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"),
          Pre => Has_Element (C, I);
   end Test_OK;

   package Test_Wrong_Number_Of_Parameters is
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

      function Element (C : Container) return Integer is
        (C.Content (1).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"),
          Pre => Has_Element (C, 1);
   end Test_Wrong_Number_Of_Parameters;

   package Test_Missing_Constant_Ref is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Element => Element_1);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Element_1 (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
      with Pre => Has_Element (C, I);

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"),
          Pre => Has_Element (C, I);
   end Test_Missing_Constant_Ref;

   package Test_Bad_First_Param is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record;

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element");
   end Test_Bad_First_Param;

   package Test_Bad_Second_Param is
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

      function Element (C : Container; I : Float) return Integer is
        (C.Content (Integer (I)).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element");
   end Test_Bad_Second_Param;

   package Test_Bad_Return_Type is
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

      function Element (C : Container; I : Natural) return Float is
        (Float (C.Content (I).all))
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"),
          Pre => Has_Element (C, I);
   end Test_Bad_Return_Type;

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
begin
   null;
end;
