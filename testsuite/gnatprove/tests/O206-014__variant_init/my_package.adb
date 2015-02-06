package body My_Package
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


end My_Package;
