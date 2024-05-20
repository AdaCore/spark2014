package P with
   SPARK_Mode
is

   type T (F, L : Natural) is private with
     Predicate => F <= L;
   --  Should be visible

private
   pragma SPARK_Mode (Off);
   type T (F, L : Natural) is record
      V : Natural;
   end record with
     Ghost_Predicate => F <= V and V <= L;
   --  Should not be visible
end P;
