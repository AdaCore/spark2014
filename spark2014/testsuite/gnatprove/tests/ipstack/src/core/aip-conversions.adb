------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with System.Storage_Elements;

package body AIP.Conversions is

   ---------
   -- Ofs --
   ---------

   function Ofs (A : System.Address; Offset : Integer) return System.Address is
      use type System.Storage_Elements.Storage_Offset;
   begin
      return A + System.Storage_Elements.Storage_Offset (Offset);
   end Ofs;

   ----------
   -- Diff --
   ----------

   function Diff (A : System.Address; B : System.Address) return Integer is
      use type System.Storage_Elements.Storage_Offset;
   begin
      return Integer (A - B);
   end Diff;

   ------------
   -- Memcpy --
   ------------

   procedure Memcpy
     (Dst : System.Address;
      Src : System.Address;
      Len : Integer)
   with
     SPARK_Mode => Off
   is
      type Mem is array (Positive range 1 .. Len) of Character;
      Dst_M : Mem;
      for Dst_M'Address use Dst;
      pragma Import (Ada, Dst_M);

      Src_M : Mem;
      for Src_M'Address use Src;
      pragma Import (Ada, Src_M);
   begin
      Dst_M := Src_M;
   end Memcpy;

end AIP.Conversions;
