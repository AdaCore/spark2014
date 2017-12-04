package body Communication with SPARK_Mode,
  Refined_State => (State => Ring_Buffer.Bla)
is
   procedure P is null;

   package body Ring_Buffer
     with Refined_State => (Bla => R.Bla2)
   is
      package body R
        with Refined_State => (Bla2 => null)
      is
      end R;
   end Ring_Buffer;

end Communication;
