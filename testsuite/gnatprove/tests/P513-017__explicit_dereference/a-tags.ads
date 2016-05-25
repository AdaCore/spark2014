with System.Storage_Elements;

package Ada.Tags is

   type Tag is private;

private

   package SSE renames System.Storage_Elements;

   type Offset_To_Top_Function_Ptr is
     access function (This : System.Address) return SSE.Storage_Offset;

   type Interface_Data_Element is record
      Offset_To_Top_Func : Offset_To_Top_Function_Ptr;
   end record;

   type Interfaces_Array is array (Natural range <>) of Interface_Data_Element;

   type Interface_Data (Nb_Ifaces : Positive) is record
      Ifaces_Table : Interfaces_Array (1 .. Nb_Ifaces);
   end record;

   type Interface_Data_Ptr is access all Interface_Data;
   --  Table of abstract interfaces used to give support to backward interface
   --  conversions and also to IW_Membership.

   type Prim_Ptr is access procedure;
   type Address_Array is array (Positive range <>) of Prim_Ptr;

   subtype Dispatch_Table is Address_Array (1 .. 1);
   --  Used by GDB to identify the _tags and traverse the run-time structure
   --  associated with tagged types. For compatibility with older versions of
   --  gdb, its name must not be changed.

   type Tag is access all Dispatch_Table;

   type Type_Specific_Data (Idepth : Natural) is record
      Interfaces_Table : Interface_Data_Ptr;
   end record;

   type Type_Specific_Data_Ptr is access all Type_Specific_Data;

   type Dispatch_Table_Wrapper is record
      TSD : System.Address;
   end record;

   type Dispatch_Table_Ptr is access all Dispatch_Table_Wrapper;

   function Displace (This : System.Address) return System.Address;

   function DT return Dispatch_Table_Ptr;

end Ada.Tags;
