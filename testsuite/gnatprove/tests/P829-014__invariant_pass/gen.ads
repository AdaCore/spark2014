package Gen is

   type T1 is tagged record
      Aaa : Natural := 0;
      Bbb : Natural := 100;
   end record;

   procedure Swap_T1 (X1 : in out T1);

   generic
      type D is new T1 with private;
   procedure Swap_View_Conversion (X : in out D);

end Gen;
