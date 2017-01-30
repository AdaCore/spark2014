package body Array_Arith
  with SPARK_Mode
is

   procedure Init (X : out T) is
      function Ident (Y : Natural) return Natural;
      function Ident (Y : Natural) return Natural is
      begin
         return Y;
      end Ident;
   begin
      X(1) := Ident(1);
      X(2) := Ident(2);
      X(3) := Ident(3);
      X(4) := Ident(4);
      X(5) := Ident(5);
      X(6) := Ident(6);
      X(7) := Ident(7);
      X(8) := Ident(8);
      X(9) := Ident(9);
      X(10) := Ident(10);
   end Init;

   procedure Init2 (X : out T) is
      One : Integer := 1;
      function Ident (Y : Natural) return Natural;
      function Ident (Y : Natural) return Natural is
      begin
         return Y + One;
      end Ident;
   begin
      X(1) := Ident(1);
      X(2) := Ident(2);
      X(3) := Ident(3);
      X(4) := Ident(4);
      X(5) := Ident(5);
      X(6) := Ident(6);
      X(7) := Ident(7);
      X(8) := Ident(8);
      X(9) := Ident(9);
      X(10) := Ident(10);
   end Init2;

   procedure Init3 (X : out T) is
      One : Integer := 1;
      function Ident (Y : Natural) return Natural;
      procedure Local;
      procedure Local is
      begin
         X(1) := Ident(1);
         X(2) := Ident(2);
         X(3) := Ident(3);
         X(4) := Ident(4);
         X(5) := Ident(5);
         X(6) := Ident(6);
         X(7) := Ident(7);
         X(8) := Ident(8);
         X(9) := Ident(9);
         X(10) := Ident(10);
      end Local;
      function Ident (Y : Natural) return Natural is
      begin
         return Y + One;
      end Ident;
   begin
      Local;
   end Init3;

   procedure Zero (X : out T) is
      procedure Put_A_Zero (Y : out Natural);
      procedure Put_A_Zero (Y : out Natural) is
      begin
         Y := 0;
      end Put_A_Zero;
   begin
      Put_A_Zero (X(1));
      Put_A_Zero (X(2));
      Put_A_Zero (X(3));
      Put_A_Zero (X(4));
      Put_A_Zero (X(5));
      Put_A_Zero (X(6));
      Put_A_Zero (X(7));
      Put_A_Zero (X(8));
      Put_A_Zero (X(9));
      Put_A_Zero (X(10));
   end Zero;

end Array_Arith;
