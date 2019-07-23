package body Private_Pointer with SPARK_Mode is
   package body Mode_On is
      procedure Set (X : T; Y : Integer) is
      begin
         X.all := My_Int (Y);
      end Set;
   end Mode_On;

   procedure Main is
   begin
      X_4 := Mode_On.Uninit_Alloc;
      Mode_On.Set (X_4, 5);
      pragma Assert (Mode_On.Get (X_4) = 5);
      Mode_On.Set (X_4, 6);
      pragma Assert (Mode_On.Get (X_4) = 6);
   end Main;
end Private_Pointer;
