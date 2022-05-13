package P is
   package Private_Types is
      type T1 (Capacity : Integer) is private;
      function "=" (X, Y : T1) return Boolean;
      type T2 is private;
      function "=" (X, Y : T2) return Boolean;

   private
      pragma SPARK_Mode (Off);
      type Int_Access is access Integer;
      type T1 (Capacity : Integer) is record
         Content : Int_Access;
      end record;
      function "=" (X, Y : T1) return Boolean is
        (X.Capacity = Y.Capacity and then X.Content = Y.Content);
      type T2 is record
         Content : Int_Access;
      end record;
      function "=" (X, Y : T2) return Boolean is
        (X.Content = Y.Content);
   end Private_Types;

   use Private_Types;

   subtype My_T1 is T1 (10);

   function My_Capacity (L : My_T1) return Integer
   with Post => My_Capacity'Result = 10;

   function Identity1 (L : My_T1) return My_T1
   with Post => Identity1'Result = L;

   function Identity2 (L : T2) return T2
   with Post => Identity2'Result = L;
end P;
