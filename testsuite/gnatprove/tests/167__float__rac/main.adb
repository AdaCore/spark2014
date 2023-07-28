with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   procedure Check (B : Boolean) is
   begin
      if B then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;
   end Check;

   generic
      type F is digits <>;
   procedure Test;

   procedure Test is
      H : F := 0.5;
      X : F := 41.5;
      Res : F;

   begin
      Res := +X;
      Check (Res = 41.5);

      Res := H + X;
      Check (Res = 42.0);

      Res := -X;
      Check (Res = -41.5);

      Res := H - X;
      Check (Res = -41.0);

      Res := X - H;
      Check (Res = 41.0);

      Res := X * H;
      Check (Res = 20.75);

      Res := X / H;
      Check (Res = 83.0);

      Check (H < X);
      Check (H <= X);
      Check (X > H);
      Check (X >= H);
      Check (X /= H);
      Check (not (X = H));

      Check (Integer (X) = 42);
      Check (Integer (H) = 1);
      Check (X = F(41) + 0.5);
      Check (F (Integer (X)) = 42.0);

      Res := F'Min (X, H);
      Check (Res = H);
      Res := F'Max (X, H);
      Check (Res = X);

      Res := F'Succ (X);
      Check (F'Pred (Res) = X);
      Res := F'Pred (X);
      Check (F'Succ (Res) = X);
   end Test;

   procedure F_Test is new Test (Float);
   procedure LF_Test is new Test (Long_Float);
   procedure LLF_Test is new Test (Long_Long_Float);

begin
   F_Test;
   LF_Test;
   LLF_Test;
end Main;
