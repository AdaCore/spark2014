procedure Main
  with
    SPARK_Mode => On
is
   function First return Integer with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function Last return Integer with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Post => Last'Result >= First;

   subtype My_Int is Integer range First .. Last;

   procedure Call_P (I : Integer; P : not null access procedure (X : My_Int)) with
     Global => null,
     Pre => I in First .. Last
   is
   begin
      P (I);
   end Call_P;
begin
   null;
end Main;
