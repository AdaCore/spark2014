package body Red_Black_Trees with SPARK_Mode is

   procedure Rotate_Left (T : in out Tree) is
      Tnew : Tree := T.Right;
   begin
      T.Right := Tnew.Left;
      Tnew.Left := T;
      T := Tnew;
   end Rotate_Left;

   procedure Rotate_Right (T : in out Tree) is
      Tnew : Tree := T.Left;
   begin
      T.Left := Tnew.Right;
      Tnew.Right := T;
      T := Tnew;
   end Rotate_Right;

   procedure Balance (T : in out Tree) is
   begin
      if T.Color = Black
        and then T.Left /= null
        and then T.Left.Color = Red
      then
         if T.Left.Left /= null
           and then T.Left.Left.Color = Red
         then
            Rotate_Right (T);
            T.Left.Color := Black;
         elsif T.Left.Right /= null
           and then T.Left.Right.Color = Red
         then
            Rotate_Left (T.Left);
            Rotate_Right (T);
            T.Left.Color := Black;
         end if;
      elsif T.Color = Black
        and then T.Right /= null
        and then T.Right.Color = Red
      then
         if T.Right.Left /= null
           and then T.Right.Left.Color = Red
         then
            Rotate_Right (T.Right);
            Rotate_Left (T);
            T.Right.Color := Black;
         elsif T.Right.Right /= null
           and then T.Right.Right.Color = Red
         then
            Rotate_Left (T);
            T.Right.Color := Black;
         end if;
      end if;
   end Balance;

   procedure Insert_Rec (T : in out Tree; V : Integer) with
     Post => T /= null
   is
   begin
      if T = null then
         T := new Tree_Cell'(Value => V,
                             Color => Red,
                             Left  => null,
                             Right => null);
      elsif T.Value = V then
         return;
      elsif T.Value > V then
         Insert_Rec (T.Left, V);
      else
         Insert_Rec (T.Right, V);
      end if;

      Balance (T);
   end Insert_Rec;

   procedure Insert (T : in out Tree; V : Integer) is
   begin
      Insert_Rec (T, V);
      T.Color := Black;
   end Insert;

end Red_Black_Trees;
