with Ada.Text_IO;

package Pkg is
   function Func (X : Integer) return Integer is (X + 1);
   procedure Put_Line (S : String) renames Ada.Text_IO.Put_Line;
end Pkg;
