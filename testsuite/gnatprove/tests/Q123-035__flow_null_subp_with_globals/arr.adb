package body Arr is

   type Length_T is range 0 .. 1000;
   subtype Index_T is Length_T range 1 .. Length_T'Last;

   type T is array (Index_T) of Integer;

   Buffer_Len : Length_T;
   Buffer     : T;

   --  We pretend to initialize Buffer through
   --  Fake_Initialize_Buffer_Buffer_With_Global setting Buffer as a global
   --  output but the procedure is a null procedure.
   procedure Initialize_With_Global (L : Length_T)
     with Global => (Output => (Buffer_Len, Buffer))
   is
      procedure Fake_Initialize_Buffer_With_Global is null
        with Global => (Output => Buffer);
   begin
      Fake_Initialize_Buffer_With_Global;
      for I in Index_T range Index_T'First .. L loop
         Buffer (I) := Integer (I);
      end loop;
      Buffer_Len := L;
   end Initialize_With_Global;

   --  Similar to the above, but with Depends (instead of Global) on the inner
   --  subprogram.
   procedure Initialize_With_Depends (L : Length_T)
     with Global => (Output => (Buffer_Len, Buffer))
   is
      procedure Fake_Initialize_Buffer_With_Depends is null
        with Depends => (Buffer => null);
   begin
      Fake_Initialize_Buffer_With_Depends;
      for I in Index_T range Index_T'First .. L loop
         Buffer (I) := Integer (I);
      end loop;
      Buffer_Len := L;
   end Initialize_With_Depends;

end Arr;
