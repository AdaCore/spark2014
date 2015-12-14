package body List_Allocator with
  SPARK_Mode
is
   package body M is
   begin
      Model.Available := 1;
      Model.Allocated := 0;
   end M;

end List_Allocator;
