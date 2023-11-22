with Interfaces; use Interfaces;
package Test with SPARK_Mode is

   type UInt4 is mod 2**4;

   procedure Enable_Interrupt;

   type INT_Group is array (0 .. 7) of UInt4
     with Volatile_Full_Access, Size => 32, Component_Size => 4;

   type IO_BANK is record
      GPIO        : aliased Unsigned_64;
      INTR        : INT_Group;
   end record
     with Volatile;
   for IO_BANK use record
      GPIO              at 0 range 0 .. 63;
   end record;

   IO_BANK_Periph : aliased IO_BANK;

end Test;
