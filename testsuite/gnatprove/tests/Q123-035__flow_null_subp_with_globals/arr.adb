package body Arr is

   type T is array (0 .. 1000) of Integer;

   Buffer : T;

   --  We pretend to initialize Buffer through
   --  Fake_Initialize_Buffer_Buffer_With_Global setting Buffer as a global
   --  output but the procedure is a null procedure.
   procedure Initialize_With_Global
     with Global => (Output => Buffer)
   is
      procedure Fake_Initialize_Buffer_With_Global is null
        with Global => (Output => Buffer);
   begin
      Fake_Initialize_Buffer_With_Global;
   end Initialize_With_Global;

   --  Similar to the above, but with Depends (instead of Global) on the inner
   --  subprogram.
   procedure Initialize_With_Depends
     with Global => (Output => Buffer)
   is
      procedure Fake_Initialize_Buffer_With_Depends is null
        with Depends => (Buffer => null);
   begin
      Fake_Initialize_Buffer_With_Depends;
   end Initialize_With_Depends;

end Arr;
