package body Test is 

   procedure Basic_Loop (X : in out Integer)
   is
   begin
      loop
         X := X + 1;
         X := X / 2;
      end loop;
   end Basic_Loop;

   procedure Is_Prime (N : Positive;
                       P : out Boolean)
   is
   begin
      for I in Positive range 2 .. N / 2 loop
         if N mod I = 0 then
            P := False;
            return;
         end if;
      end loop;
      P := True;
   end Is_Prime;

   procedure Loop_Exits (X : in out Integer;
                         Y : in Integer)
   is
   begin
      My_Loop : loop
         X := 0;
         for I in Integer range 0 .. 10 loop
            X := I;
            exit My_Loop when X > Y;
         end loop;
         X := X;
      end loop My_Loop;
      X := 5;
   end Loop_Exits;

   procedure While_Loop (X : in Natural;
                         Y : out Integer)
   is
   begin
      Y := 0;
      while X /= Y loop
         Y := Y + 1;
      end loop;
   end While_Loop;

   function Bergeretti_Fig9_Correct (B, P : Integer) return Integer
   is
      C, D, Q, R, W, X, Y : Integer;
   begin
      C := P; D := B;
      X := 0; Y := 1;
      while D /= 1 loop
         Q := C / D; R := C mod D;
         W := X - Q * Y;
         C := D; D := R;
         X := Y; Y := W;
      end loop;
      if Y < 0 then
         Y := Y + P;
      end if;
      return Y;
   end Bergeretti_Fig9_Correct;

   function Bergeretti_Fig9_Incorrect (B, P : Integer) return Integer
   is
      C, D, Q, R, W, X, Y : Integer;
   begin
      C := P; D := B;
      X := 0; Y := 1;
      while D /= 1 loop
         Q := C / D;
         W := X - Q * Y;
         C := D; D := R;
         X := Y; Y := W;
      end loop;
      if Y < 0 then
         Y := Y + P;
      end if;
      return Y;
   end Bergeretti_Fig9_Incorrect;

   procedure Stable_Test_01 (X : out Natural)
   is
   begin
      for I in Natural range 0 .. 100 loop
         for J in Natural range 5 .. 10 loop
            X := I;
         end loop;
      end loop;
   end Stable_Test_01;

   procedure Stable_Test_02 (X : out Natural)
   is
   begin
      for I in Natural range 0 .. 100 loop
         for J in Natural range 5 .. 10 loop
            X := J;
         end loop;
      end loop;
   end Stable_Test_02;

   type The_World is (Foo, Bar, Baz);
   subtype Void is The_World range Bar .. Foo;

   procedure For_Test_01 (X : out Natural)
   is
   begin
      for Great_Justice in Void loop
         X := 0;
      end loop;
   end For_Test_01;

   procedure For_Test_02 (X : out Natural)
   is
   begin
      for Great_Justice in The_World loop
         X := 0;
         exit when great_justice > Bar;
      end loop;
   end For_Test_02;

   procedure Basic_With_Exit (X : in out Natural)
   is
   begin
      loop
         X := X * 2;
         if X > 10 then
            return;
         end if;
         X := X - 1;
      end loop;
   end Basic_With_Exit;

end Test;
