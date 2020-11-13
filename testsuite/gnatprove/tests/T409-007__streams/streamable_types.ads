with Ada.Streams;

package Streamable_Types with SPARK_Mode is
   use Ada;

   type Int is new Integer;

   procedure Print (Stream : not null access Streams.Root_Stream_Type'Class;
                    Item   : Int);

   procedure Parse (Stream : not null access Streams.Root_Stream_Type'Class;
                    Item   : out Int);

   for Int'Read use Parse;
   for Int'Write use Print;

   Parsing_Error : exception;
end Streamable_Types;
