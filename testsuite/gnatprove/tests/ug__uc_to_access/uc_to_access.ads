with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;
with System;     use System;

package UC_To_Access with SPARK_Mode => On is
   type Int_Access is access all Integer;

   function Uns_To_Int_Access is new Ada.Unchecked_Conversion (Unsigned_64, Int_Access);
   --  Accepted with warnings
   function Uns_From_Int_Access is new Ada.Unchecked_Conversion (Int_Access, Unsigned_64);
   --  Rejected

   C1 : constant Int_Access := Uns_To_Int_Access (30);

   function Addr_To_Int_Access is new Ada.Unchecked_Conversion (Address, Int_Access);
   --  Accepted with warnings
   function Addr_From_Int_Access is new Ada.Unchecked_Conversion (Int_Access, Address);
   --  Rejected

   Addr : Address with Import;
   C2 : constant Int_Access := Addr_To_Int_Access (Addr);

   type PS_Access is access Integer;

   function Uns_To_PS_Access is new Ada.Unchecked_Conversion (Unsigned_64, PS_Access);
   --  Rejected
end UC_To_Access;
