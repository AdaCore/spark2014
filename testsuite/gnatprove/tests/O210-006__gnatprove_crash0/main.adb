procedure Main
with SPARK_Mode
is
   type Array_Type is array (Natural range <>) of Integer;

   type Discr_Type (Discr : Positive) is
     record
       M_Array : Array_Type (0 .. Discr);
     end record;

   procedure Set_Discr_Type (D : out Discr_Type) is
   begin
      D.M_Array := (others => 0);
   end;

   D : Discr_Type (15);

begin

   Set_Discr_Type (D);


end Main;
