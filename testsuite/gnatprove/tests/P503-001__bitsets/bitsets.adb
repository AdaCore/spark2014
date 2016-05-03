package body Bitsets is

   ---------
   -- Add --
   ---------

   function Add (S : Set; E : Element) return Set is
      Res : Set := S;
   begin
      Res (E) := True;
      return Res;
   end Add;

   procedure Add (S : in out Set; E : Element) is
   begin
      S (E) := True;
   end Add;

   -----------
   -- Empty --
   -----------

   function Empty return Set is
   begin
      return (others => False);
   end Empty;

   ---------
   -- Mem --
   ---------

   function Mem (S : Set; E : Element) return Boolean is (S (E));

   ------------
   -- Remove --
   ------------

   function Remove (S : Set; E : Element) return Set is
      Res : Set := S;
   begin
      Res (E) := False;
      return Res;
   end Remove;

   procedure Remove (S : in out Set; E : Element) is
   begin
      S (E) := False;
   end Remove;

   -----------
   -- Union --
   -----------

   function Union (A, B : Set) return Set is
   begin
      return A or B;
   end Union;

   procedure Union (A : in out Set; B : Set) is
   begin
      A := A or B;
   end Union;



end Bitsets;
