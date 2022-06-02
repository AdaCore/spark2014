with Types; use Types;

package Test
   with SPARK_Mode
is

   function Bar is new Foo (Byte);

   pragma Annotate (GNATprove, Always_Return, Bar);

   function Test (Buffer : Bytes) return Byte is
      (Bar (Buffer));

end Test;
