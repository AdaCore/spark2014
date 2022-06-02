package Types
   with SPARK_Mode
is

   type Byte is mod 2**8;
   type Bytes is array (Positive range <>) of Byte;

   generic
      type Int is mod <>;
   function Foo (Buffer : Bytes) return Int;

   pragma Annotate (GNATprove, Always_Return, Foo);

end Types;
