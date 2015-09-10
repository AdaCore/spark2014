---------------------------------------------------------------------------
-- FILE    : hermes-oid.ads
-- SUBJECT : Specification of Object Identifier package.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Hermes.OID is

   -- Component_Array holds object identifiers as an array of component values.
   Maximum_Component_Count : constant := 15;
   type    Component_Type is range 0 .. Integer'Last;
   subtype Component_Count_Type is Natural range 0 .. Maximum_Component_Count;
   subtype Component_Index_Type is Positive range 1 .. Maximum_Component_Count;
   type    Component_Array is array(Component_Index_Type range <>) of Component_Type;
   type    Status_Type is (Success, Invalid_Root, Invalid_Second_Level, Insufficient_Space);

   type Object_Identifier is private;

   -- Converts an OID in the form of separate components into an abstract object identifier.
   procedure To_Object_Identifier
     (Separates : in Component_Array; Result : out Object_Identifier; Status : out Status_Type)
     with Depends => ( (Result, Status) => Separates);

   -- Returns the number of components inside the given object identifier.
   function Component_Count(Identifier : Object_Identifier) return Component_Count_Type;

   -- Converts an object identifier into an array of separate components. Returns in the
   -- Number_Of_Components parameter the number of components used. If there is a problem with
   -- the conversion (due to lack of space) a count of zero is returned. Unused space in the
   -- Result array is filled with zero component values.
   --
   -- TODO: Would this be better as a function returning Component_Array?
   procedure To_Separates
     (Identifier           : in  Object_Identifier;
      Result               : out Component_Array;
      Number_Of_Components : out Component_Count_Type)
     with
       Depends => ( (Result, Number_Of_Components) => (Identifier, Result) );

   -- Converts an object identifier into an array of raw bytes. Returns in the Octet_Count
   -- parameter the number of bytes used. If there is a problem with the conversion (for
   -- example, due to lack of space) a count of zero is returned. Unused space in the Result
   -- array is filled with zero byte values; although if a failure occurs the Result array has
   -- an indeterminate value.
   --
   -- TODO: Would this be better as a function returning Octet_Array?
   procedure To_Octet_Array
     (Identifier : in Object_Identifier; Result : out Octet_Array; Octet_Count : out Natural)
     with
       Depends => ( (Result, Octet_Count) => (Result, Identifier) );

private

   -- 1.3.6.14.311.5.1007
   -- Suppose 0.40... Then first byte of encoded OID would = 40*0 + 40 = 40
   -- Suppose 1.0...  Then first byte of encoded OID would = 40*1 + 0  = 40 is ambiguous!
   -- Rule: If the first OID subcomponent is 0 or 1. The second subcomponent is 0 .. 39. Thus
   -- if the first OID subcomponent is 2, the second subcomponent must be 175 at most because
   -- (2*40 + 175 = 255).

   subtype Root_Component_Type is Component_Type range 0 .. 2;
   subtype Second_Level_Component_Type is Component_Type range 0 .. 175;
   subtype Other_Index_Type is Component_Index_Type range 1 .. Component_Index_Type'Last - 2;
   subtype Other_Count_Type is Integer range 0 .. Other_Index_Type'Last;
   type    Other_Component_Array is array(Other_Index_Type) of Component_Type;

   type Object_Identifier is
      record
         Root_Component         : Root_Component_Type;
         Second_Level_Component : Second_Level_Component_Type;
         Other_Components       : Other_Component_Array;
         Other_Component_Count  : Other_Count_Type;
      end record;

end Hermes.OID;
