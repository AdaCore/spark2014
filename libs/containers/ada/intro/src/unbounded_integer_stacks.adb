package body Unbounded_Integer_Stacks is

   function Create return Stack  is
      output : Stack (Chunk_Size);
   begin
      output.Cont_Ptr.all := (others => Default_Value);
      output.Index := 1;
      return output;
   end Create;

   procedure Enlarge (S : in out Stack) is
      New_Size : Positive := S.Cont_Ptr'Length + Chunk_Size;
      New_Ptr : Content_Ref := new Content_Type (1 .. New_Size);
      Old_Used_Elements  : Natural := S.Index - 1;
   begin
      New_Ptr (1 .. Old_Used_Elements) := S.Cont_Ptr (1 .. Old_Used_Elements);
      New_Ptr (S.Index .. New_Size) := (others => Default_Value);
      S.Cont_Ptr := New_Ptr;
   end Enlarge;

   function Is_Empty (S : Stack) return Boolean is
   begin
      if S.Index = 1 then
         return True;
      else
         return False;
      end if;
   end Is_Empty;

   function Is_Full (S : Stack) return Boolean is
   begin
      if S.Index = S.Cont_Ptr'Length + 1 then
         return True;

         --  Because index points to the first free empty cell

      else
         return False;
      end if;
   end Is_Full;

   function Peek (S : Stack) return Integer is
   begin
      return S.Cont_Ptr (S.Index - 1);
   end Peek;

   function Pop (S : in out Stack) return Integer is
      output : Integer := Default_Value;
   begin
      Pop (S, output);
      return output;
   end Pop;

   procedure Pop (S : in out Stack; X : out Integer)  is
      New_Index : Natural := S.Index - 1;
   begin
      X := S.Cont_Ptr (New_Index);
      S.Cont_Ptr (New_Index) := Default_Value;

      --  cleaning the used slot

      S.Index := New_Index;
   end Pop;

   function Push (S : Stack; X : Integer) return Stack is
      output : Stack := S;
   begin
      if Is_Full (output) then
         Enlarge (output);
      end if;
      output.Cont_Ptr (output.Index) := X;
      output.Index := output.Index + 1;
      return output;
   end Push;

   procedure Push (S : in out Stack; X : Integer) is
   begin
      if Is_Full (S) then
         Enlarge (S);
      end if;
      S.Cont_Ptr (S.Index) := X;
      S.Index := S.Index + 1;
   end Push;

   --  Push a new element on the stack

end Unbounded_Integer_Stacks;
