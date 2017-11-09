package body C.B is

   protected type BufferType is
      entry Get;
   end BufferType;

   Buffer : BufferType;

   protected body BufferType is
      entry Get when True is
      begin
         null;
      end Get;
   end BufferType;

   procedure Receive is
   begin
      Buffer.Get;
   end Receive;

end C.B;
