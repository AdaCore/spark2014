package Bytes is

   type U32 is mod 2**32;

   generic
      type Payload is private;
   function Extract (Data : aliased Payload) return U32;

   generic
      type Payload is private;
   procedure Extract_Proc (Data : aliased out Payload);

end Bytes;
