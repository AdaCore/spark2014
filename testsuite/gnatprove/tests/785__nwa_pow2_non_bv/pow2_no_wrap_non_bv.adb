procedure Pow2_No_Wrap_Non_Bv with SPARK_Mode is
   type Non_Binary is mod 2 ** 16 - 1
   with
     Annotate => (GNATprove, No_Wrap_Around),
     Annotate => (GNATprove, No_Bitwise_Operations);

   subtype Small_Exponent is Natural range 0 .. 16;

   procedure Pow2 (Exp : Small_Exponent; Result : out Non_Binary)
   with Pre => True
   is
   begin
      Result := Non_Binary'(2) ** Exp;
   end Pow2;

begin
   declare
      Result : Non_Binary;
   begin
      Pow2 (16, Result);
   end;
end Pow2_No_Wrap_Non_Bv;
