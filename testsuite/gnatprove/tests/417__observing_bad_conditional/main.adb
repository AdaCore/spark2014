procedure Main with SPARK_Mode is
   type Tree;
   type Tree_Acc is access Tree;
   type Tree is record
      Value : Integer;
      Left  : Tree_Acc;
      Right : Tree_Acc;
   end record;

   procedure Do_Something (X : access constant Tree)
     with Global => null, Import, Always_Terminates => True;

   procedure Test (T : Tree_Acc) with Global => null;
   procedure Test2 (T : Tree_Acc) with Global => null;
   procedure Test3 (T : Tree_Acc) with Global => null;
   procedure Test4 (T : Tree_Acc) with Global => null;
   procedure Test5 (T : Tree_Acc) with Global => null;
   procedure Test6 (T : Tree_Acc) with Global => null;

   procedure CTest (T : Tree_Acc) with Global => null;
   procedure CTest2 (T : Tree_Acc) with Global => null;
   procedure CTest3 (T : Tree_Acc) with Global => null;
   procedure CTest4 (T : Tree_Acc) with Global => null;
   procedure CTest5 (T : Tree_Acc) with Global => null;
   procedure CTest6 (T : Tree_Acc) with Global => null;
   procedure CTest7 (T : Tree_Acc) with Global => null;

   procedure Test (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2
         then T.Right.Left
         else T.Right.Right); --  Ok
   begin
      Do_Something (Y);
   end Test;

   procedure Test2 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2 then T.Left else T.Right); --  Bad.
   begin
      Do_Something (Y);
   end Test2;

   procedure Test3 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2 then T else T.Right); --  Bad
   begin
      Do_Something (Y);
   end Test3;

   procedure Test4 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2 then T.Left.Left.Right else T.Left.Right); --  Bad
   begin
      Do_Something (Y);
   end Test4;

   procedure Test5 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2 then T.Right else T.Left.Right); --  Ok.

   begin
      Do_Something (Y);
   end Test5;

   procedure Test6 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value = 2
         then T.Left.Right.Left
         else T.Left.Right.Right); --  Ok.
   begin
      Do_Something (Y);
   end Test6;

   procedure CTest (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 0 => T.Right.Left,
            when 1 => T.Right.Right,
            when 2 => T.Right,
            when others => T.Right.Left.Right); --  Ok
   begin
      Do_Something (Y);
   end CTest;

   procedure CTest2 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 0 => T.Right.Left,
            when 1 => T.Right.Right,
            when 2 => T.Left,
            when others => T.Right.Left.Right); --  Bad.
   begin
      Do_Something (Y);
   end CTest2;

   procedure CTest3 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 0 => T,
            when 1 => T.Right,
            when 42 => T.Right.Right,
            when others => T.Right.Right.Right); --  Bad
   begin
      Do_Something (Y);
   end CTest3;

   procedure CTest4 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 3 .. 7 => T.Right.Left,
            when 14 .. 16 => T.Left.Right,
            when others => T.Right); -- Ok

   begin
      Do_Something (Y);
   end CTest4;

   procedure CTest5 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 42 .. 111 => T.Left.Left.Right,
            when 6 .. 36 => T.Left.Right,
            when others => T.Left.Left.Left); --  Bad
   begin
      Do_Something (Y);
   end CTest5;

   procedure CTest6 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (case X.Value is
            when 142 .. 257 => T.Left.Right,
            when 7 .. 49 => T.Left.Right.Right,
            when others => T.Left.Right.Left.Right.Right); -- Ok

   begin
      Do_Something (Y);
   end CTest6;

   procedure CTest7 (T : Tree_Acc) is
      X : access Tree := T.Left.Left;
      Y : access constant Tree :=
        (if X.Value >= -2 then
           (case X.Value is
               when -1 .. 0 => T.Left.Right.Left.Right,
               when 36 .. 42 => T.Left.Right.Left.Left.Right,
               when 117 .. 257 =>
                 T.Left.Right.Left.Left.Left.Left.Left,
               when 421 .. 65537 =>
                 T.Left.Right.Left.Left.Left.Right.Left.Left.Left,
               when others =>
                 T.Left.Right.Left.Right.Left.Right.Left.Right.Left.Left
           )
         else
           (case X.Value is
               when -56 => T.Left.Right.Left.Left,
               when others => T.Left.Right.Left.Left.Left
           )
        );
      --  Ok.

   begin
      Do_Something (Y);
   end CTest7;

begin
   null;
end Main;
