procedure Test with SPARK_Mode is
   procedure Test_Element is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
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
        (C.Content (I).all);

      C : Container := (Max => 5, Content => (1 .. 5 => new Integer'(1)));
   begin
      for E of C loop
         C.Content (1).all := E; --  OK: when iterating using Element, there is no guarantee that the object is not tampered with
      end loop;
   end;

   procedure Test_Constant_Reference is
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
        (C.Content (I));

      C : Container := (Max => 5, Content => (1 .. 5 => new Integer'(1)));
   begin
      for E of C loop
         C.Content (1).all := E; --  ERROR: C was observed
      end loop;
   end;
begin
   null;
end;
