-- We show that a parameter is usually supposed to have a RW permission at the call site with disregard to the callee modes.


with Ada.Unchecked_Deallocation;

with Ada.Text_IO;
use Ada.Text_IO;

Procedure N05 with SPARK_Mode is

  type Int_Acc is access all integer;


------
  procedure Out_A (A : out Int_Acc) with Pre => True is
  begin
	  Put_Line("hi");
  end Out_A;
------

------
  procedure In_A (A : in Int_Acc) with Pre => True is
  begin
	  Put_Line("hi");
  end In_A;
------

------
  procedure IN_IN (A : in Int_Acc; B : in Int_Acc; C : out integer) with Pre => True  is
  begin
	  C := A.all + B.all;
  end IN_IN;
------

------
  procedure Out_IN (A : in out Int_Acc; B : in Int_Acc; C : out integer) is
  begin
	  C := A.all + B.all;
  end Out_IN;
------

  AA0, AA1 : Int_Acc;
  B : Int_Acc;
  C : integer;
  a0, a1 : aliased integer;

begin
  AA0 := a0'access;
  AA1 := a1'access;
  AA0.all := 2;
  B.all := 3;
  B := AA0;  -- AA0 and B alias. AA0 should have W permissions. AA0 suffixes have No permission.
  Out_A (AA0); -- ICI: insufficient permission for "A" when returning from "Out_A", expected at least "Read_Write", got "Write_Only". Why we do not claim the missing read permission for AA here. This whows an error at Out_A def site.
  B := AA1;
 -- In_A (AA1);  -- ICI
 -- In_In (AA0, B, C);
 -- Out_In (AA0, B, C); -- ERROR: The analyzer expects A to have RW permission (not Write only) at this call site eventhough the formal parameter has only out mode.
end N05;
