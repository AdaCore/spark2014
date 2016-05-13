with Ada.Unchecked_Conversion;

with System.Storage_Elements; use System.Storage_Elements;

package body Ada.Tags is

   function To_Type_Specific_Data_Ptr is
     new Ada.Unchecked_Conversion (System.Address, Type_Specific_Data_Ptr);

   --------------
   -- Displace --
   --------------

   function Displace (This : System.Address) return System.Address is
      Iface_Table : Interface_Data_Ptr;
      Obj_Base    : System.Address;
      Obj_DT      : Dispatch_Table_Ptr;

   begin
      Obj_Base    := This;
      Obj_DT      := DT;
      Iface_Table := To_Type_Specific_Data_Ptr (Obj_DT.TSD).Interfaces_Table;

      --  Case of Static value of Offset_To_Top

      Obj_Base := Obj_Base +
        Iface_Table.Ifaces_Table (1).Offset_To_Top_Func.all (Obj_Base);

      return Obj_Base;
   end Displace;

   --------
   -- DT --
   --------

   function DT return Dispatch_Table_Ptr is
   begin
      return null;
   end DT;

end Ada.Tags;
