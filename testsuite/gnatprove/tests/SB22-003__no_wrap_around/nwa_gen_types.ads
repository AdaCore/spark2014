package NWA_Gen_Types with SPARK_Mode is

   type NvU24_Wrap is mod 2 ** 24 with Size => 24;

   generic
      type BASE_TYPE is mod <>;
   package Nv_Types_Generic
   is
      type N_TYPE is new BASE_TYPE with Annotate => (GNATprove, No_Wrap_Around);
   end Nv_Types_Generic;

   package NvU24_Types is new Nv_Types_Generic (BASE_TYPE => NvU24_Wrap);

   type NvU24 is new NvU24_Types.N_TYPE;

end NWA_Gen_Types;
