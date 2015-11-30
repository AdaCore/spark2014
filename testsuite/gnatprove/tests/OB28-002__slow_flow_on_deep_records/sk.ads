package SK
is

   type Byte is mod 2**8;
   for Byte'Size use 8;

   type Word16 is mod 2**16;
   for Word16'Size use 16;

   type Word32 is mod 2**32;
   for Word32'Size use 32;

   type Word64 is mod 2**64;
   for Word64'Size use 64;

   --  Size of one page (4k).
   Page_Size : constant := 4096;

end SK;
