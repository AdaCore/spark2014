with Ada.Unchecked_Deallocation;

package body Simple_Sets
  with SPARK_Mode => Off
is

   procedure Free is
      new Ada.Unchecked_Deallocation (Set_Record, Set);


   ----------------
   -- Equivalent --
   ----------------

   function Equivalent (A, B : Set) return Boolean is
   begin
      for I in 1 .. Number_Of_Members (A) loop
         if not Is_Member (B, Get_Member (A, I)) then
            return False;
         end if;
      end loop;
      for J in 1 .. Number_Of_Members (B) loop
         if not Is_Member (A, Get_Member (B, J)) then
            return False;
         end if;
      end loop;
      return True;
   end Equivalent;

   -----------------------
   -- Number_Of_Members --
   -----------------------

   function Number_Of_Members (S : Set) return Natural is
      Current_Record : Set := S;
      Count : Natural := 0;
   begin
      while Current_Record /= null loop
         Count := Count + 1;
         Current_Record := Current_Record.Next;
      end loop;
      return Count;
   end Number_Of_Members;

   ---------------
   -- Is_Member --
   ---------------

   function Is_Member (S : Set; E : Integer) return Boolean is
      Current_Record : Set := S;
      Found : Boolean := False;
   begin
      while Current_Record /= null loop
         Found := Current_Record.Element = E;
         exit when Found;
         Current_Record := Current_Record.Next;
      end loop;
      return Found;
   end Is_Member;

   -----------------
   -- Find_Member --
   -----------------

   function Find_Member (S : Set; E : Integer) return Natural is
      Current_Record : Set := S;
      Count : Natural := 0;
   begin
      while Current_Record /= null loop
         Count := Count + 1;
         exit when Current_Record.Element = E;
      end loop;
      return Count;
   end Find_Member;

   ----------------
   -- Get_Member --
   ----------------

   function Get_Member (S : Set; N : Positive) return Integer is
      Current_Record : Set := S;
   begin
      for I in 2 .. N loop
         Current_Record := Current_Record.Next;
      end loop;
      return Current_Record.Element;
   end Get_Member;

   ----------------
   -- Add_Member --
   ----------------

   procedure Add_Member (S : in out Set; E : Integer) is
   begin
      if not Is_Member (S, E) then
         S := new Set_Record'(E, S);
      end if;
   end Add_Member;

   -----------------
   -- Destroy_Set --
   -----------------

   procedure Destroy_Set (S : out Set) is
      Next_Record : Set;
   begin
      while S /= null loop
         Next_Record := S.Next;
         Free (S);
         S := Next_Record;
      end loop;
   end Destroy_Set;

end Simple_Sets;
