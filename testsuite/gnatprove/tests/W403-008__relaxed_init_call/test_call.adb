procedure Test_Call with SPARK_Mode is

   type My_Int is new Integer with Relaxed_Initialization;

   procedure Incr (Y : My_Int; X : out My_Int) with
     Pre  => Y < My_Int'Last,
     Post => X = Y + 1;

   procedure Incr (Y : My_Int; X : out My_Int) is
   begin
      X := Y + 1;
   end Incr;

   procedure Call_Incr (X : in out My_Int) with
     Pre  => X < My_Int'Last;

   procedure Call_Incr (X : in out My_Int) is
      Y : constant My_Int := X;
   begin
      Incr (X, X);
      pragma Assert (X = Y + 1);
   end Call_Incr;

   procedure Call_Incr_2 (X : in out My_Int) with
     Pre  => X < My_Int'Last;

   procedure Call_Incr_2 (X : in out My_Int) is
      Y : constant My_Int := X;
   begin
      Incr (Y, X);
      pragma Assert (X = Y + 1);
   end Call_Incr_2;

begin
   null;
end Test_Call;
