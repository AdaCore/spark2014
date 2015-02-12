procedure Main
with SPARK_Mode
is
   type Array_Type is array (Natural range <>) of Boolean;
   pragma Pack (Array_Type);

   type Discr_Type (Discr : Positive) is
     record
       M_Array : Array_Type (0 .. Discr);
     end record;

   generic
      D : in out Discr_Type;
   procedure G_Set_Discr_Type;

   procedure G_Set_Discr_Type is
   begin
      D.M_Array := (others => False);
   end;

   D : Discr_Type (15);
   procedure Set_Discr_Type is new G_Set_Discr_Type (D => D);

begin

   Set_Discr_Type;


end Main;
