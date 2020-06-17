package body Pkg1
   with SPARK_Mode
is


    procedure Read_Arr(Arr : out Array_T) is
    begin
        Arr (Arr'First .. 3) := (others => 0);

        for I in NvU8 range 4 .. Arr'Last loop
            Arr (I) := NvU32(I) + 5;
         pragma Loop_Invariant
           (for all K in Arr'First .. I => Arr (K)'Initialized);
        end loop;

    end Read_Arr;

    procedure Read_Arr2(Arr : out Array_T) is
    begin

      for I in NvU8 range Arr'First .. 3 loop
         Arr (I) := NvU32(I) + 5;
         pragma Loop_Invariant
           (for all K in Arr'First .. I => Arr (K)'Initialized);
      end loop;

      for I in NvU8 range 4 .. Arr'Last loop
         Arr (I) := NvU32(I) + 5;
         pragma Loop_Invariant
           (for all K in Arr'First .. I => Arr (K)'Initialized);
      end loop;

    end Read_Arr2;


end Pkg1;
