
with Ada.Text_IO;
use Ada.Text_IO;

procedure simple with SPARK_Mode is
   type Int_Ptr is access all Integer;
   type Int_Cst_Ptr is access constant Integer;
   type Int_Ptr_Ptr is access all Int_Ptr;
   B : Int_Ptr_Ptr;
   A : aliased Int_Ptr;
   C : integer;
   X : access Integer;
   Y : Int_Ptr;
   D,E : Int_Ptr_Ptr;
   no_important_var0 : aliased integer;
   no_important_var1 : aliased Int_Ptr;
begin
   -- Initializing variables to avoid read but never assigned warning.
   Y := no_important_var0'access;
   E := no_important_var1'access;
   -- Testing if a named access type variable can be assigned to an anonymous one.
   X := Y;  -- OK
   --A.all := 2;
   B := A'access;
   -- Testing assignment on an address taken variable.
   A.all := 3;  -- ERROR
   -- Testing reading from an address taken variable.
   C := A.all;  -- ERROR
   -- Dereference assignment on B having the address of A (ako A.all := 42).
   B.all.all := 42;  -- OK
   -- Testing reading from an address taken variable when using image suffix.
   Put_Line (integer'image(A.all));  -- ERROR
   --
   D := B;  -- move B to D.
   -- Testing reading from a pointer after a move.
   C := B.all.all;  -- ERROR: B has been moved so has no access now. Permissions has been assigned to C.
   -- Re-assigning the moved pointer.
   B := E;  -- B gets RW permissions after this instruction.
   -- Testing reading from a pointer after re-assigning it after a move.
   C := B.all.all;  -- OK: reading from B is ok after re-assignment.

end simple;
