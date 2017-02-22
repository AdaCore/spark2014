package body Arr is

   type Length_T is range 0 .. 1000;
   subtype Index_T is Length_T range 1 .. Length_T'Last;

   type T is array (Index_T) of Integer;

   Buffer_Len : Length_T;
   Buffer     : T;

   procedure Initialize (L : Length_T)
     with Global => (Output => (Buffer_Len, Buffer))
   is
      procedure Fake_Initialize_Buffer is null
        with Global => (Output => Buffer);
   begin
      Fake_Initialize_Buffer;
      for I in Index_T range Index_T'First .. L loop
         Buffer (I) := Integer (I);
      end loop;
      Buffer_Len := L;
   end Initialize;

end Arr;
