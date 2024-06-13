with System; use System;
with System.Storage_Elements; use System.Storage_Elements;

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists;

package Logging_Storage_Models is

   type Native_Storage_Model is limited record
      null;
   end record
     with Storage_Model_Type;

   type Logging_Address is new System.Address;

   type Region is record
      Addr : Integer;
      Size : Storage_Count;
      Id   : Integer;
   end record;

   package Object_Ids is new SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists
     (Region);

   type Logging_Storage_Model is limited record
      Name             : Unbounded_String;
      Count_Write      : Integer := 0;
      Count_Read       : Integer := 0;
      Count_Allocate   : Integer := 0;
      Count_Deallocate : Integer := 0;
      Display_Log      : Boolean := False;
      Ids              : Object_Ids.List;
   end record
     with Storage_Model_Type =>
       (Address_Type          => Logging_Address,
        Allocate              => Logging_Allocate,
        Deallocate            => Logging_Deallocate,
        Copy_To               => Logging_Copy_To,
        Copy_From             => Logging_Copy_From,
        Storage_Size          => Logging_Storage_Size,
        Null_Address          => Logging_Null_Address);

   Logging_Null_Address : constant Logging_Address :=
     Logging_Address (System.Null_Address);

   procedure Logging_Allocate
     (Model           : in out Logging_Storage_Model;
      Storage_Address : out Logging_Address;
      Size            : Storage_Count;
      Alignment       : Storage_Count);

   procedure Logging_Deallocate
     (Model           : in out Logging_Storage_Model;
      Storage_Address : Logging_Address;
      Size            : Storage_Count;
      Alignment       : Storage_Count);

   procedure Logging_Copy_To
     (Model  : in out Logging_Storage_Model;
      Target : Logging_Address;
      Source : System.Address;
      Size   : Storage_Count);

   procedure Logging_Copy_From
     (Model  : in out Logging_Storage_Model;
      Target : System.Address;
      Source : Logging_Address;
      Size   : Storage_Count);

   function Logging_Storage_Size
     (Model : Logging_Storage_Model)
   return Storage_Count;

   Model : Logging_Storage_Model;

   No_Model : Native_Storage_Model;

end Logging_Storage_Models;
