with NWA_Gen_Types; use NWA_Gen_Types;

procedure NWA_Generic with SPARK_Mode is

   type NV_CPUPROC_UPROC_InstrC_OFFS_FIELD is new NvU24;

   Ucode_Instr_Offset_In_UPROC : NV_CPUPROC_UPROC_InstrC_OFFS_FIELD := 0;
begin
   while Ucode_Instr_Offset_In_UPROC < NV_CPUPROC_UPROC_InstrC_OFFS_FIELD'Last loop
      Ucode_Instr_Offset_In_UPROC := Ucode_Instr_Offset_In_UPROC + 4;
   end loop;
end NWA_Generic;
