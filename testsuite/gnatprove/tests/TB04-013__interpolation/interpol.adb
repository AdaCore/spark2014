package body Interpol
  with SPARK_Mode
is
   procedure Repro (DA, DX : Arg; F : Monotonic_Incr_Func; K : Index)
     with Global => null,
          Pre => DA in 0 .. DX
            and then DX > 0
            and then F'Last > 0
            and then K in 1 .. F'Last - 1
   is
      DY : constant Integer := F(K+1).Y - F(K).Y;
      E  : constant Integer := F(K).Y + DA * DY / DX;
   begin
      pragma Assert (E in F(K).Y .. F(K+1).Y);
   end Repro;

   procedure Repro2 (DA, DX : Arg; F : Monotonic_Incr_Func2; K : Index)
     with Global => null,
          Pre => DA in 0 .. DX
            and then DX > 0
            and then F'Last > 0
            and then K in 1 .. F'Last - 1
   is
      DY : constant Integer := F(K+1).Y - F(K).Y;
      E  : constant Integer := F(K).Y + DA * DY / DX;
   begin
      pragma Assert (E in F(K).Y .. F(K+1).Y);
   end Repro2;

end Interpol;
