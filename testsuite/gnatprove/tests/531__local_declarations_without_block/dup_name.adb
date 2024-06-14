with Text_IO;
procedure Dup_Name is

   function F (X : Integer) return Integer is
   begin
      case X is
         when 1 =>
            Y : constant Integer := X*X;
            return Y;
         when 2 =>
            Y : constant Integer := X*X;
            return Y;
         when others =>
            Y : constant Integer := X*X;
            return Y;
      end case;
   end F;

begin
   A : constant Integer := F (1);
   use Text_IO;
   Put_Line (A'Image);
   B : constant Integer := F (2);
   Put_Line (B'Image);
   C : constant Integer := F (3);
   Put_Line (C'Image);
end Dup_Name;
