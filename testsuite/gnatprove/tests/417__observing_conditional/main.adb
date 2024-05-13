procedure Main with SPARK_Mode is
   type Tree;
   type Tree_Acc is access Tree;
   type Tree is record
      Value : Integer;
      Left  : Tree_Acc;
      Right : Tree_Acc;
   end record;

   function Left_N (T : access constant Tree; N : Natural)
                    return access constant Tree
   is (if N = 0 or else T = null then T else Left_N (T.Left, N - 1))
     with Subprogram_Variant => (Structural => T);

   procedure Test (T : Tree_Acc) with Global => null;
   procedure Test2 (T : Tree_Acc) with Global => null;

   procedure Test (T : Tree_Acc) is
   begin
      if T = null
        or else T.Left = null
        or else T.Left.Left = null
        or else T.Left.Right = null
      then
         return;
      end if;
      declare
         X : access constant Tree :=
           (if T.Value >= 42
            then Left_N (T.Left.Right, 36).Left
            else T.Left.Left);
      begin
         T.Right.Value := Left_N (X, 53).Value;
      end;
   end Test;

   procedure Test2 (T : Tree_Acc) is
   begin
      if T = null
        or else T.Right = null
        or else T.Right.Right = null
        or else T.Right.Right.Left = null
        or else T.Right.Right.Left.Right = null
      then
         return;
      end if;
      declare
         X : access constant Tree :=
           (case T.Value is
               when 0 => Left_N (T.Right.Right, 36).Left,
               when 1 => T.Right.Right.Left,
               when others => T.Right.Right.Left.Right);
      begin
         T.Right.Left.Value := Left_N (X, 41).Value;
         T.Left.Value := Left_N (X, 79).Value;
      end;
   end Test2;

begin
   null;
end Main;
