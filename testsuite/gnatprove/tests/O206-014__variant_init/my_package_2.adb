package body My_Package_2
with SPARK_Mode
is
   procedure Init_Variant
     (CI : in  Integer;
      XI : in  Integer;
      V  : out Variant_Type)
   is
   begin
      V.M_C := CI;

      case V.M_V is
         when A =>
            V.M_A := XI;
         when B =>
            V.M_B := XI;
      end case;
   end Init_Variant;

   --  Placing pragma Annotate after the body also works
   pragma Annotate (GNATprove, False_Positive, """V.M_A"" might not be initialized in ""Init_Variant""", "...");
   pragma Annotate (GNATprove, False_Positive, """V.M_B"" might not be initialized in ""Init_Variant""", "...");

end My_Package_2;
