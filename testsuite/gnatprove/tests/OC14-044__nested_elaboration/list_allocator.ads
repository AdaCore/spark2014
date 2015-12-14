package List_Allocator with
  SPARK_Mode
is
   pragma Elaborate_Body;

   package M is
      type T is record
         Available : Integer;
         Allocated : Integer;
      end record;

      Model : T;
   end M;

end List_Allocator;
