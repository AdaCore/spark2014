package My_Package
with SPARK_Mode
is
   type Enum_Type is (A, B);
   type Variant_Type (M_V : Enum_Type) is
     record
       M_C : Integer;
       case M_V is
          when A =>
             M_A : Integer;
          when B =>
             M_B : Integer;
       end case;
     end record;


   pragma Warnings (Off, "analyzing unreferenced procedure");
   procedure Init_Variant
     (CI : in  Integer;
      XI : in  Integer;
      V  : out Variant_Type)
   with Pre => CI /= 0;

   pragma Annotate (GNATprove, False_Positive, """V.M_A"" might not be initialized in ""Init_Variant""", "...");
   pragma Annotate (GNATprove, False_Positive, """V.M_B"" might not be initialized in ""Init_Variant""", "...");

end My_Package;
