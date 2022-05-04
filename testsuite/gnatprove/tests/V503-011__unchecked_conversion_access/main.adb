with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;
with System; use System;
procedure Main with SPARK_Mode => on is
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

   type Two_32 is record
      X, Y : Unsigned_32;
   end record
     with Size => 64;

   function Two_32_To_Int_Access is new Ada.Unchecked_Conversion (Two_32, Int_Access);
   --  Rejected
   function Two_32_From_Int_Access is new Ada.Unchecked_Conversion (Int_Access, Two_32);
   --  Rejected

   type PS_Access is access Integer;

   function Uns_To_PS_Access is new Ada.Unchecked_Conversion (Unsigned_64, PS_Access);
   --  Rejected
   function Uns_From_PS_Access is new Ada.Unchecked_Conversion (PS_Access, Unsigned_64);
   --  Rejected

   type Cst_Access is access constant Integer;

   function Uns_To_Cst_Access is new Ada.Unchecked_Conversion (Unsigned_64, Cst_Access);
   --  Accepted with warnings
   function Uns_From_Cst_Access is new Ada.Unchecked_Conversion (Cst_Access, Unsigned_64);
   --  Rejected

   C3 : constant Cst_Access := Uns_To_Cst_Access (30);

   function Addr_To_Cst_Access is new Ada.Unchecked_Conversion (Address, Cst_Access);
   --  Accepted with warnings
   function Addr_From_Cst_Access is new Ada.Unchecked_Conversion (Cst_Access, Address);
   --  Rejected

   C4 : constant Cst_Access := Addr_To_Cst_Access (Addr);

   type Rec is record
      F, G : Int_Access;
   end record
     with Size => 128;

   function Uns_To_Rec is new Ada.Unchecked_Conversion (Unsigned_128, Rec);
   --  Rejected
   function Uns_From_Rec is new Ada.Unchecked_Conversion (Rec, Unsigned_128);
   --  Rejected

   type Subp_Access is access function (X : Integer) return Integer;

   function Uns_To_Subp_Access is new Ada.Unchecked_Conversion (Unsigned_64, Subp_Access);
   --  Rejected
   function Uns_From_Subp_Access is new Ada.Unchecked_Conversion (Subp_Access, Unsigned_64);
   --  Rejected
begin
null;
end Main;
