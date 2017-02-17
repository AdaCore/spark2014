package body Slice_Test_3
  with SPARK_Mode => On
is

   procedure Slice_Dynamic (A : in out Arr;  I, J, K, L: in Index)
   is
   begin
      if (J - I = L - K) then

         --  in generated why, sliding here has wrong argument for
         --  new_first:

         A (I .. J) :=
           A (K .. L);
      end if;
   end Slice_Dynamic;

end Slice_Test_3;
