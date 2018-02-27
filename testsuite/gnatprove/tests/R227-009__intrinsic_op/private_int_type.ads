package Private_Int_Type with
  SPARK_Mode
is
   type My_Int is private;
   function "<=" (Left, Right : My_Int) return Boolean with
     Global => null;
   function ">" (Left, Right : My_Int) return Boolean with
     Global => null;

   My_Zero : constant My_Int;
   My_One  : constant My_Int;

private
   pragma SPARK_Mode (Off);

   type My_Int is new Integer;

   function Hide (X : My_Int) return My_Int is (X);

   My_Zero : constant My_Int := Hide (0);
   My_One  : constant My_Int := Hide (1);

   pragma Import (Intrinsic, "<=");
   pragma Import (Intrinsic, ">");

end Private_Int_Type;
