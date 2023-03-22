package Geometry with
  SPARK_Mode
is
   type Shape is tagged record
      Pos_X, Pos_Y : Float;
   end record;

   function Valid (S : Shape) return Boolean is
     (S.Pos_X in -100.0 .. 100.0 and S.Pos_Y in -100.0 .. 100.0);

   procedure Operate (S : in out Shape) with
     Pre'Class => Valid (S);

   procedure Set_Default (S : in out Shape) with
     Post'Class => Valid (S);

   procedure Set_Default_Repeat (S : in out Shape) with
     Post'Class => Valid (S);

   procedure Set_Default_No_Post (S : in out Shape);

   type Rectangle is new Shape with record
      Len_X, Len_Y : Float;
   end record;

   function Valid (S : Rectangle) return Boolean is
     (Valid (Shape (S)) and S.Len_X in 0.0 .. 10.0 and S.Len_Y in 0.0 .. 10.0);

   procedure Operate (S : in out Rectangle);

   procedure Set_Default (S : in out Rectangle);

   procedure Set_Default_Repeat (S : in out Rectangle) with
     Post'Class => Valid (S);

   procedure Set_Default_No_Post (S : in out Rectangle) with
     Post'Class => Valid (S);

end Geometry;
