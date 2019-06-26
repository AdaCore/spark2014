with General_Strings;
with Ada.Containers.Formal_Doubly_Linked_Lists;
package Loggers with
  SPARK_Mode
is
   type Logger is tagged private;
   type Cursor is private;

      package String_Lists is
     new Ada.Containers.Formal_Doubly_Linked_Lists
	(Element_Type => General_Strings.Bounded_String,
	 "="          => General_Strings."=");

     function Get_Error (Object : Logger; Position : Cursor) return String with
       Global => null,
        Pre => Has_Error (Object, Position);
     function Has_Error (Object : Logger; Position : Cursor) return Boolean with
     Global => null;

private
   type Cursor is new String_Lists.Cursor;
   type Logger is tagged record
      Error_Log : String_Lists.List (10);
   end record;
end Loggers;
