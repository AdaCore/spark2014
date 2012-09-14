with Ada.Text_IO; use Ada.Text_IO;
with Ada.Assertions; use Ada.Assertions;
with Ada.Exceptions; use Ada.Exceptions;

package body Unbounded_Stacks is

   function Create (I              : Positive := Chunk_Size; Default : Item_Type)
                    return Stack  is
      output                       : Stack (I);
   begin
      Default_Value := Default;
      output.Cont_Ptr.all := (others => Default_Value);
      output.Index := 1;
      return output;
   end Create;

   function Is_Empty (S            : Stack)
                      return Boolean is
   begin
      if S.Index = 1 then
         return True;
      else
         return False;
      end if;
   end Is_Empty;

   function Is_Full (S             : Stack)
                     return Boolean is
   begin
      if S.Index = S.Cont_Ptr'Length + 1 then
         --  cause index points to the first free empty cell
         return True;
      else
         return False;
      end if;
   end Is_Full;

   procedure Push (S               : in out Stack; X : Item_Type) is
   begin
      if Is_Full (S) then
         Enlarge (S);
      end if;
      S.Cont_Ptr (S.Index) := X;
      S.Index := S.Index + 1;
   end Push;
   --  push a new element on the stack

   procedure Pop (S                : in out Stack; X : out Item_Type)  is
      New_Index                    : Natural := S.Index - 1;
   begin
      X := S.Cont_Ptr (New_Index);
      S.Cont_Ptr (New_Index) := Default_Value;
      --  cleaning the occupied slot
      S.Index := New_Index;
   end Pop;

   function Pop (S                 : in out Stack)
                 return Item_Type is
      output                       : Item_Type := Default_Value;
   begin
      Pop (S, output);
      return output;
   end Pop;

   function Peek (S                : Stack)
                  return Item_Type is
      output                       : Item_Type := Default_Value;
   begin
      if not Is_Empty (S) then
         output := S.Cont_Ptr (S.Index - 1);
      end if;
      return output;
   end Peek;

   function Push (S                : Stack; X : Item_Type)
                  return Stack is
      output                       : Stack := S;
   begin
      Push (output, X);
      return output;
   end Push;

   procedure Enlarge (S           : in out Stack;
                      Delta_Size   : Positive := Chunk_Size) is
      New_Size                     : Positive :=  S.Cont_Ptr'Length + Delta_Size;
      New_Ptr                      : Content_Ref := new Content_Type (1 .. New_Size);
      Old_Used_Elements            : Natural := S.Index - 1;
   begin
      New_Ptr (1 .. Old_Used_Elements) := S.Cont_Ptr (1 .. Old_Used_Elements);
      New_Ptr (S.Index .. New_Size) := (others => Default_Value);
      S.Cont_Ptr := New_Ptr;
   end Enlarge;

   procedure test_Pop_When_Empty (S : in out Stack) is
      X                            : Item_Type;
   begin
      X := Pop (S);
      Put_Line ("Error              : Pop on empty stack does not raise exception");
   exception
         --      When Assert_Failure =>
      when others =>
         Put_Line ("Ok             : Pop on empty rstack raises exception");

   end test_Pop_When_Empty;

end Unbounded_Stacks;
