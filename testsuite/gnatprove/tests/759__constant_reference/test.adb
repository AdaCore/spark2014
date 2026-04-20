procedure Test with SPARK_Mode is
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
   function Constant_Reference (C : Container; I : Natural) return
   not null access constant Integer is
     (C.Content (I))
   with Pre => Has_Element (C, I);

   C : Container := (Max => 5, Content => (1 .. 5 => new Integer'(1)));
begin
   for E of C loop
      if E /= 1 then
         raise Program_Error;
      end if;
   end loop;

   pragma Assert (for all E of C => E = 1);
end;
