with Ada.Strings.Unbounded;
with Ada.Strings.Unbounded.Text_IO;

with Ada.Strings.Wide_Unbounded;
with Ada.Strings.Wide_Unbounded.Wide_Text_IO;

with Ada.Strings.Wide_Wide_Unbounded;
with Ada.Strings.Wide_Wide_Unbounded.Wide_Wide_Text_IO;

package body P is
   protected body PT is

      procedure Put_Unbounded_String is
      begin
         Ada.Strings.Unbounded.Text_IO.Put (Ada.Strings.Unbounded.Null_Unbounded_String);
      end;

      procedure Put_Wide_Unbounded_String is
      begin
         Ada.Strings.Wide_Unbounded.Wide_Text_IO.Put (Ada.Strings.Wide_Unbounded.Null_Unbounded_Wide_String);
      end;

      procedure Put_Wide_Wide_Unbounded_String is
      begin
         Ada.Strings.Wide_Wide_Unbounded.Wide_Wide_Text_IO.Put (Ada.Strings.Wide_Wide_Unbounded.Null_Unbounded_Wide_Wide_String);
      end;
   end;
end;
