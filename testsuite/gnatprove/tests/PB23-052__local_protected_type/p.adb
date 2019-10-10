package body P is
   procedure Dummy (D : Ada.Containers.Count_Type) is
      protected type PT is
         private
         X : My_Vectors.Vector (D-2); --@RANGE_CHECK:FAIL
      end PT;

      protected body PT is
      end PT;
   begin
      null;
   end;
end;
