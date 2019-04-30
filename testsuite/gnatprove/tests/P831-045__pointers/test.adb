
with Ada.Text_IO;
use Ada.Text_IO;



procedure test with SPARK_Mode is
   type Int_Ptr is access all Integer; -- pool-specific type definition (no all nor constant modifier).
   type Int_Ptr2 is access all Integer;
   type Int_Ptr_Ptr is access all Int_Ptr;
   type Int_Cst_Ptr is access constant Integer;
   x, y, z, n : aliased integer;
   A : access Integer;
   B, C : Int_Ptr;
   D : String := "hello";
   E : aliased Int_Ptr;
   Ptr : Int_Ptr;
   x0, x1 : aliased integer;
   var : Int_Ptr_Ptr;
   varPtr, varPtr2 : Int_Ptr2; -- named pool-specific variables.
   K : Int_Ptr;


  T : access integer renames A;
  I : Int_Ptr renames B;
--------------
  procedure f (P : in out Int_Ptr; Q : in out Int_Ptr; x0 : in out Integer) is
  type Int_Ptr1 is access all Integer;
  -- x0 : aliased integer;
  begin
	--P := x0'access;
	--P := Q.all'access;
	P.all := 15;
  end f;
--------------


--------------
  function g (P : in String) return integer is
  begin
	return P'length;
  end g;

  procedure h (P : in out Int_Ptr) is
  begin
	P.all := 42;
  end h;
--------------


--------------
  function returnPointer (X : Int_Ptr_Ptr) return Int_Ptr is
    varPtr : Int_Ptr;
  begin
	varPtr := X.all;
	return varPtr;
  end returnPointer;
--------------



--------------
  procedure returnPointer2 (Y : out Int_Ptr) is
	X : Int_Ptr;
  begin
	Y := X;
  end returnPointer2;
--------------


--------- Testing is out parameters of anonymous access type ----------
  procedure RW (Z : access constant integer; W : access integer; var : integer) is
  begin
	W.all := var;
  end RW;

begin
  A := x'access;
  E := n'access;
  var := E'access;
  --B := A;
  --C := B;
  --B := C;
  y := B.all;
  --B := x0'access;
  f(B, C, x0);
  z := g(D);
  h(C);
  A := returnPointer(var);
  Ptr := var.all;
  -- returnPointer2(A);
  -- testing assignments between named pool-specific types.
  varPtr := varPtr2;
  varPtr := x1'access;
  K := Ptr;
end test;


