------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with System.Machine_Code; use System.Machine_Code;

package body AIP.Time_Types is

   package PPC_Clock is

      type Cycle_Type is mod 2 ** 64;

      function Get_Cycle_Counter return Cycle_Type;
      --  Clock implementation based on PowerPC cycle counter

   end PPC_Clock;

   package body PPC_Clock is

      type Uns32 is mod 2**32;

      -------------
      -- Get_Tbl --
      -------------

      function Get_Tbl return Uns32
      is
         Res : Uns32;
      begin
         Asm ("mftb %0",
              Outputs  => Uns32'Asm_Output ("=r", Res),
              Volatile => True);
         return Res;
      end Get_Tbl;

      -------------
      -- Get_Tbu --
      -------------

      function Get_Tbu return Uns32
      is
         Res : Uns32;
      begin
         Asm ("mftbu %0",
              Outputs  => Uns32'Asm_Output ("=r", Res),
              Volatile => True);
         return Res;
      end Get_Tbu;

      -----------------------
      -- Get_Cycle_Counter --
      -----------------------

      function Get_Cycle_Counter return Cycle_Type is
         Lo  : Uns32;
         Hi  : Uns32;
         Hi2 : Uns32;
      begin
         Hi := Get_Tbu;
         loop
            Lo := Get_Tbl;
            Hi2 := Get_Tbu;
            exit when Hi2 = Hi;
            Hi := Hi2;
         end loop;
         return Cycle_Type (Hi) * 2**32 or Cycle_Type (Lo);
      end Get_Cycle_Counter;

   end PPC_Clock;

   ---------
   -- Now --
   ---------

   function Now return Time is
      use type PPC_Clock.Cycle_Type;

   begin
      return Time (PPC_Clock.Get_Cycle_Counter / (Clock_Hz / 1_000));
   end Now;

end AIP.Time_Types;
