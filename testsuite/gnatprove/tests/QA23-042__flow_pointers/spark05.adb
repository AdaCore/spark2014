with Ada.Text_IO;
use Ada.Text_IO;

procedure Spark05 is

   package Data is
      type Point is record
         X,Y : aliased Integer;
      end record;
      type AI is access Integer;
      type AP is access Point;
      type Meta is record
         A : aliased AP;
      end record;
      type AM is access Meta;
      function CreatePoint(X: AI; Y: AI) return Point;
   end Data;

   package body Data is
      function CreatePoint (X: AI; Y: AI) return Point --peeked X and Y
      is (X=>X.all, Y=>Y.all); --no move for X and Y : ok

   end Data;
   use Data;

   X : aliased Integer := 10;
   Y : aliased Integer := 14;
   AX : AI := new Integer'(X); -- move of (X) occurs here.
   AY : AI := new Integer'(Y); -- move of (Y) occurs here.
   P : aliased Point;
   M : aliased Meta;
   AAM : aliased AM;
   P2 : aliased Point := (X=> 102, Y=>103);
   getX : Integer;
   getY : Integer;
begin
   P := CreatePoint(X=>AX,Y=>AY); --peek of AX, AY

   Put_Line ("P.X =" & Integer'Image(P.X)
             & ", P.Y =" & Integer'Image(P.Y)
             & ", AX.all =" & Integer'Image(AX.all)
             & ", AY.all =" & Integer'Image(AY.all)); --DEBUG

   AY.all := 42;
   AX.all := 40;

   declare
      Tmp : AP := new Point'(P);
   begin
      M := (A=>Tmp);
   end;
   AAM := new Meta'(M);

   getX := AAM.all.A.all.X; --move of AAM.all.A.all.X;
   getY := AAM.all.A.all.Y; --move of AAM.all.A.all.Y;

   Put_Line ("P.X =" & Integer'Image(P.X)
             & ", P.Y =" & Integer'Image(P.Y)
             & ", AX.all =" & Integer'Image(AX.all)
             & ", AY.all =" & Integer'Image(AY.all)
             & ", getX =" & Integer'Image(getX)
             & ", getY =" & Integer'Image(getY)); --DEBUG


   declare
      Tmp : AP := new Point'(P2);
   begin
      AAM.all := (A=>Tmp);
   end;
                              --assign to AAM.all --lifting restriction
   getX := AAM.all.A.all.X;   --move of AAM.all.A.all.X: legal here
   getY := AAM.all.A.all.Y;   --move of AAM.all.A.all.Y: legal here

   Put_Line ("P.X =" & Integer'Image(P.X)
             & ", P.Y =" & Integer'Image(P.Y)
             & ", AX.all =" & Integer'Image(AX.all)
             & ", AY.all =" & Integer'Image(AY.all)
             & ", getX =" & Integer'Image(getX)
             & ", getY =" & Integer'Image(getY)); --DEBUG

end Spark05;
